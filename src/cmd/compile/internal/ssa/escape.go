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
		call *Value
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
		kind       kindEscape
	}

	kindEscape = uint8
)

const (
	unchecked kindEscape = iota
	safe
	mayEscape
	mustEscape
)

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
				kind:       unchecked,
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
	heapAllocs := []newobject{}

	// Lookup for calls to runtime.newobject (i.e. heap allocations).
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			if !isHeapAlloc(v) {
				continue
			}

			ref := refMap[v].references[0].value
			newobj := newobject{
				call: newobjectCall{
					addr:   v.Args[0].Args[1],
					offptr: v.Args[0].Args[0],
					store:  v.Args[0],
					call:   v,
				},
				ret: newobjectRet{
					offptr: ref.Args[0],
					load:   ref,
				},
			}

			heapAllocs = append(heapAllocs, newobj)
			root := refMap[newobj.ret.load]
			escapes(root)
			esc := root.kind == safe
			log.Println("Is safe to be stack-allocated?", esc)
		}
	}

	for _, h := range heapAllocs {
		if refMap[h.ret.load].kind == safe {
			_ = h.call.offptr.Args[0]

			// Load will be converted to OffPtr
			// h.ret.load.reset(OpOffPtr)
			// h.ret.load.AddArg(sp)
			// h.ret.load.AuxInt = h.ret.load.Type.Size()
			// h.ret.load.Type = types.NewPtr(h.ret.load.Type)

			// Each value related to heap alloc must be reseted.
			// h.ret.offptr.resetArgs()
			// h.call.call.resetArgs()
			// h.call.store.resetArgs()
			// h.call.offptr.resetArgs()
			// h.call.addr.resetArgs()
		}
	}
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

			if node.kind == mayEscape {
				escapes(ref)
				node.kind = ref.kind
			}

			if node.kind == mustEscape {
				break
			}
		}
	}
}

// Check whether a node need to be analyzed or not.
func needAnalysis(node *escapeNode) (need bool) {
	// Node was already checked and thus we know if it can escape or not.
	if node.kind != unchecked {
		need = node.kind == safe
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
			node.kind = safe
			return
		}

		// If Args[0] class is ParamOut and the value being returned (Args[1])
		// is an address then the root node must escape for sure.
		switch node.value.Args[1].Type.Etype {
		case types.TUINTPTR, types.TPTR, types.TUNSAFEPTR:
			node.kind = mustEscape

		default:
			node.kind = safe
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
			node.kind = safe
			return
		}

		gcnode, ok := ref.value.Args[0].Aux.(GCNode)
		if !(ok && gcnode.StorageClass() == ClassParamOut) {
			node.kind = mayEscape
			return
		}

		// If Args[0] class is ParamOut and the value being returned (Args[1])
		// is an address then the root node must escape for sure.
		switch ref.value.Args[1].Type.Etype {
		case types.TUINTPTR, types.TPTR, types.TUNSAFEPTR:
			node.kind = mustEscape

		default:
			node.kind = safe
		}

	case OpCopy:
		node.kind = mayEscape

	case OpLoad:
		// If the returned type of OpLoad is a pointer, than it may be being
		// used for something like a return or assignment to a global variable.
		switch ref.value.Type.Etype {
		case types.TUINTPTR, types.TPTR, types.TUNSAFEPTR:
			node.kind = mayEscape
		default:
			node.kind = safe
		}

	default:
		// Set default as "must escape" to prevent from stack-allocating
		// something erroneously.
		node.kind = mustEscape
	}
}
