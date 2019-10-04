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
		block      *Block
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

	// Init refmap and keep track of each reference to a value.
	refmap := findRefs(f)

	// Keep track of each heap allocation to rewrite later.
	newobjList := []newobject{}

	// Lookup for calls to runtime.newobject (i.e. heap allocations).
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			if !isHeapAlloc(v) {
				continue
			}

			ref := refmap[v].references[0].value
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
			root := refmap[newobj.ret.load]
			escapes(root)
			esc := root.state == safe
			log.Println("Is safe to be stack-allocated?", esc)
		}
	}

	for _, n := range newobjList {
		if refmap[n.ret.load].state == safe {
			// Create new var and convert load to a new stack-allocated var.
			node := f.Frontend().Auto(n.ret.load.Pos, n.ret.load.Type)
			mem := n.ret.load.Block.NewValue1A(
				n.ret.load.Pos,
				OpVarDef,
				types.TypeMem,
				node,
				n.call.store.MemoryArg(),
			)

			sp := n.call.offptr.Args[0]
			newStackAlloc(n.ret.load, sp, mem, node)

			// Each value related to heap alloc must be reseted.
			elimHeapAlloc(n, refmap, mem)
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
	refmap := map[*Value]*escapeNode{}

	// Initialize refmap.
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			refmap[v] = &escapeNode{
				value:      v,
				block:      b,
				state:      unchecked,
				references: []*escapeNode{},
			}
		}
	}

	// Lookup for references.
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			for _, arg := range v.Args {
				refmap[arg].references = append(
					refmap[arg].references,
					refmap[v],
				)
			}
		}
	}

	return refmap
}

// Convert load value to a localaddr.
func newStackAlloc(load, sp, mem *Value, node GCNode) {
	load.reset(OpLocalAddr)
	load.AddArgs(sp, mem)
	load.Aux = node
}

// Remove the heap alloc that was replaced by a safe stack alloc.
func elimHeapAlloc(n newobject, refmap map[*Value]*escapeNode, mem *Value) {
	// Update mem state (store value).
	ref := refmap[n.call.staticcall].references[1].value
	ref.SetArg(len(ref.Args)-1, mem)

	// Force StaticCall to be considered as deadcode.
	n.call.staticcall.reset(OpInvalid)

	// Reset the remaining heap-alloc call values.
	n.call.store.resetArgs()
	n.call.addr.resetArgs()

	if isDead(n.call.offptr) {
		n.call.offptr.resetArgs()
	}

	if isDead(n.ret.offptr) {
		n.ret.offptr.resetArgs()
	}
}

func isDead(v *Value) bool {
	return v.Uses == 0
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

	default:
		node.state = safe
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
		node.state = mayEscape
	}
}
