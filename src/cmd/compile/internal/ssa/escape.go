package ssa

import (
	"cmd/compile/internal/types"
	"cmd/internal/obj"
	"log"
)

type (
	// Get the type that will be allocated, push it to the stack and call the
	// runtime function that will handle the heap allocation.
	newobjectCall struct {
		addr,
		offptr,
		store,
		staticcall *Value
	}

	// Get the new address allocated by the runtime call.
	newobjectRet struct {
		offptr,
		load *Value
	}

	newobject struct {
		call newobjectCall
		ret  newobjectRet
	}

	escapeNode struct {
		value      *Value
		references []*escapeNode
		state      nodeState
	}

	nodeState = uint8
)

const (
	unchecked nodeState = iota
	safe
	mayEscape
	mustEscape
)

// escapeAnalysis walks through the values of a function f to determine whether
// a value can safely be allocated on the stack or it escapes to the heap. This
// complements the escape analysis applied to the AST.
func escapeAnalysis(f *Func) {
	if f.Name != "foo" {
		return
	}

	// Init refMap and keep track of each reference to a value.
	refMap := findRefs(f)

	// Keep track of each heap allocation to rewrite later.
	newobjList := []newobject{}

	// Lookup for calls to runtime.newobject (i.e. heap allocations).
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			if !isHeapAlloc(v) {
				continue
			}

			ref := refMap[v].references[0].value
			newobj := newobject{
				call: newobjectCall{
					addr:       v.Args[0].Args[1],
					offptr:     v.Args[0].Args[0],
					store:      v.Args[0],
					staticcall: v,
				},
				ret: newobjectRet{
					offptr: ref.Args[0],
					load:   ref,
				},
			}

			newobjList = append(newobjList, newobj)
			root := refMap[newobj.ret.load]
			escapes(root)
			esc := root.state == safe
			log.Println("Is safe to be stack-allocated?", esc)
		}
	}

	for _, n := range newobjList {
		if refMap[n.ret.load].state == safe {
			// Both Store and StaticCall change the memory state. Thus, we need
			// to update the memory state passed to the args of each reference
			// to these two values. Since they both will be removed, the
			// current memory state will be that referenced by the store op.
			prevMemState := n.call.store.Args[2]

			storeRefs := unwrapRefs(refMap[n.call.store].references)
			revertMemState(prevMemState, n.call.store, storeRefs)

			staticcallRefs := unwrapRefs(refMap[n.call.staticcall].references)
			revertMemState(prevMemState, n.call.staticcall, staticcallRefs)

			// Load will be converted to OffPtr
			sp := n.call.offptr.Args[0]
			convertLoad(n.ret.load, sp)

			// Each value related to heap alloc must be reseted.
			cleanNewobj(n)
		}
	}
}

func isHeapAlloc(v *Value) bool {
	switch aux := v.Aux.(type) {
	case *obj.LSym:
		return v.Op == OpStaticCall &&
			isSameSym(aux, "runtime.newobject")
	default:
		return false
	}
}

// Keep track of each reference to a value.
func findRefs(f *Func) map[*Value]*escapeNode {
	refMap := map[*Value]*escapeNode{}

	// Initialize refMap.
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			refMap[v] = &escapeNode{
				value:      v,
				state:      unchecked,
				references: []*escapeNode{},
			}
		}
	}

	// Lookup for references.
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			for _, arg := range v.Args {
				refMap[arg].references = append(
					refMap[arg].references,
					refMap[v],
				)
			}
		}
	}

	return refMap
}

// Get the proper reference values from within a list of node.
func unwrapRefs(nodes []*escapeNode) (refs []*Value) {
	for _, n := range nodes {
		refs = append(refs, n.value)
	}

	return
}

// Update the mem state with a previous state passed by param and remove the
// old state from ref args.
func revertMemState(mem, value *Value, references []*Value) {
	for _, ref := range references {
		ref.Args[len(ref.Args)-1] = mem // Mem state is always the last arg (?)
		value.Uses--
	}
}

// Convert load value to a offptr.
func convertLoad(load, sp *Value) {
	t := load.Type
	s := t.Elem().Size()

	load.reset(OpOffPtr)
	load.Type = t
	load.AuxInt = s
	load.AddArg(sp)
}

// Remove the heap alloc that was replaced by a safe stack alloc.
func cleanNewobj(n newobject) {
	n.ret.offptr.reset(OpUnknown)
	n.call.staticcall.reset(OpUnknown)
	n.call.store.reset(OpUnknown)
	n.call.offptr.reset(OpUnknown)
	n.call.addr.reset(OpUnknown)
}

func escapes(node *escapeNode) {
	if !needAnalysis(node) {
		return
	}

	if len(node.references) == 0 {
		// If value doesn't have any child, it's a leaf. That means that we
		// cannot postergate the decision and thus "analyzeLeaf" must return
		// either "safe" or "mustEscape".
		analyzeLeaf(node)

	} else {
		// Else we need to check each reference to value v. We're doing this by
		// means of a DFS-like algorithm. Edges will be cutted if we found a
		// "mustEscape" value.
		for _, ref := range node.references {
			analyzeNode(node, ref)

			if node.state == mayEscape {
				escapes(ref)
				node.state = ref.state
			}

			if node.state == mustEscape {
				break
			}
		}
	}
}

// Check whether a node need to be analyzed or not.
func needAnalysis(node *escapeNode) (need bool) {
	// Node was already checked and thus we know if it can escape or not.
	if node.state != unchecked {
		need = node.state == safe
		return
	}

	switch node.value.Type.Etype {
	case types.TUINTPTR, types.TPTR, types.TUNSAFEPTR:
		// v must be analyzed
		need = true

	case types.TSSA:
		if node.value.Type.Extra.(string) != "mem" {
			need = false
		} else {
			need = true
		}

	default:
		// If v doesn't neither hold an address or changes memory state then
		// there's no chance to escape.a
		need = false
	}

	return
}

// Since we're already in a leaf that means we cannot postergate the decision
// and thus we must return either "safe" or "mustEscape" (there's no place for
// "mayEscape" in this function).
func analyzeLeaf(node *escapeNode) {
	switch node.value.Op {
	case OpStore:
		gcnode, ok := node.value.Args[0].Aux.(GCNode)
		if !(ok && gcnode.StorageClass() == ClassParamOut) {
			node.state = safe
			return
		}

		// If Args[0] class is ParamOut and the value being returned (Args[1])
		// is an address then the root node must escape for sure.
		switch node.value.Args[1].Type.Etype {
		case types.TUINTPTR, types.TPTR, types.TUNSAFEPTR:
			node.state = mustEscape

		default:
			node.state = safe
		}
	}
}

// Check if there's any chance to a value escapes from the function considering
// a reference to v.
func analyzeNode(node, ref *escapeNode) {
	switch ref.value.Op {
	case OpStore:

		// We only care for write operations, so to v escapes it first needs to
		// be being written to another value (i.e. appears as Args[1]).
		if node.value != ref.value.Args[1] {
			node.state = safe
			return
		}

		gcnode, ok := ref.value.Args[0].Aux.(GCNode)
		if !(ok && gcnode.StorageClass() == ClassParamOut) {
			node.state = mayEscape
			return
		}

		// If Args[0] class is ParamOut and the value being returned (Args[1])
		// is an address then the root node must escape for sure.
		switch ref.value.Args[1].Type.Etype {
		case types.TUINTPTR, types.TPTR, types.TUNSAFEPTR:
			node.state = mustEscape

		default:
			node.state = safe
		}

	case OpCopy:
		node.state = mayEscape

	case OpLoad:
		// If the returned type of OpLoad is a pointer, than it may be being
		// used for something like a return or assignment to a global variable.
		switch ref.value.Type.Etype {
		case types.TUINTPTR, types.TPTR, types.TUNSAFEPTR:
			node.state = mayEscape
		default:
			node.state = safe
		}

	default:
		// Set default as "must escape" to prevent from stack-allocating
		// something erroneously.
		node.state = mustEscape
	}
}
