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
// a value can safely be stack-allocated or it really escapes to the heap. This
// complements the escape analysis applied to the AST.
func escapeAnalysis(f *Func) {
	if f.Name != "foo" {
		return
	}

	// Init refmap to keep track of each reference to a value.
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

			// TODO: REMOVE!!!!
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

			precheckVal(refmap[v])
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

				precheckArg(refmap[v], refmap[arg])
			}
		}
	}

	return refmap
}

func precheckVal(node *escapeNode) {
	if isGlobal(node.value) {
		node.state = mayEscape
	}
}

func precheckArg(node, arg *escapeNode) {
	if arg.state == mustEscape ||
		isGlobal(arg.value) && !isRead(node.value, arg.value) {

		node.state = mustEscape
	}
}

// Check if an arg is somehow being read.
func isRead(v, arg *Value) bool {
	switch v.Op {
	case OpStore:
		return v.Args[1] == arg
	case OpCopy:
		return true
	default:
		return false
	}
}

// Check if v is a global var.
func isGlobal(v *Value) bool {
	return v.Op == OpAddr
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
	preVisit(node)
	if node.state != mayEscape {
		return
	}

	if len(node.references) == 0 {
		// If value doesn't have any child, it's a leaf. That means that we
		// cannot postpone the decision and thus "visitLeaf" must return
		// either "safe" or "mustEscape".
		visitLeaf(node)

	} else {
		// Else we need to check each reference to value v. We're doing this by
		// means of a DFS-like algorithm. Edges will be cutted if we found a
		// "mustEscape" value.
		for _, ref := range node.references {
			visitNode(node, ref)

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
func preVisit(node *escapeNode) {
	// Node was already checked and thus we know if it must escape or not.
	if node.state != unchecked {
		return
	}

	switch node.value.Type.Etype {
	case types.TUINTPTR, types.TPTR, types.TUNSAFEPTR:
		node.state = mayEscape

	case types.TSSA:
		if node.value.Type.Extra.(string) != "mem" {
			node.state = safe
		} else {
			node.state = mayEscape
		}

	default:
		// If v doesn't neither hold an address or changes memory state then
		// there's no chance to escape.
		node.state = safe
	}
}

// Since we're already in a leaf that means we cannot postpone the decision
// and thus we must return either "safe" or "mustEscape" (there's no place for
// "mayEscape" in this function).
func visitLeaf(leaf *escapeNode) {
	switch leaf.value.Op {
	case OpStore:
		checkOpStore(leaf, leaf, false)
	default:
		leaf.state = safe
	}
}

// Check if there's any chance to a value escapes from the function considering
// a reference to v.
func visitNode(node, ref *escapeNode) {
	switch ref.value.Op {
	case OpStore:
		checkOpStore(node, ref, true)

	case OpCopy:
		node.state = mayEscape

	case OpLoad:
		switch ref.value.Type.Etype {
		case types.TUINTPTR, types.TPTR, types.TUNSAFEPTR:
			// If the returned type of OpLoad is a pointer, than it may be being
			// used for something like a return or assignment to a global variable.
			node.state = mayEscape

		default:
			node.state = safe
		}

	default:
		node.state = mayEscape
	}
}

func checkOpStore(node, ref *escapeNode, postpone bool) {
	// We only care for read ops (i.e. node.value at args[1]) where the
	// type is a ptr to something.
	if !isRead(ref.value, node.value) {
		node.state = safe
		return
	}

	switch ref.value.Args[1].Type.Etype {
	case types.TUINTPTR, types.TPTR, types.TUNSAFEPTR:
		gcnode, ok := ref.value.Args[0].Aux.(GCNode)

		if ok && gcnode.StorageClass() == ClassParamOut {
			// Args[0] class is ParamOut and the value being returned (Args[1])
			// is an address, thus the root node must escape for sure.
			node.state = mustEscape
		} else if postpone {
			node.state = mayEscape
		} else {
			node.state = safe
		}

	default:
		node.state = safe
	}

}
