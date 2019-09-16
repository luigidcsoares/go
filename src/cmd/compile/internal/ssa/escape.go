package ssa

import (
	"cmd/compile/internal/types"
	"cmd/internal/obj"
	"fmt"
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

// escapeAnalysis walks through the values of a function f to determine whether
// a value can safely be allocated on the stack or it escapes to the heap. This
// complements the escape analysis applied to the AST.
func escapeAnalysis(f *Func) {
	if f.Name != "foo" {
		return
	}

	// Initialize refMap and lookup for each reference to a value.
	refMap := map[*Value]*escapeNode{}
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			refMap[v] = &escapeNode{
				value: v,
				kind:  unchecked,
			}

			for _, arg := range v.Args {
				refMap[arg].references = append(
					refMap[arg].references,
					refMap[v],
				)
			}
		}
	}

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
					// Load is the first reference of a value corresponding to
					// a runtime.newobject call since it is related to the
					// caller getting the returned value. The returned value
					// was placed in the stack and thus it must be loaded by using
					// the offptr (the value before the load).
					offptr: ref.Args[0],
					load:   ref,
				},
			}

			root := refMap[newobj.ret.load]
			escapes(root)
			esc := !(root.kind == mustEscape)
			fmt.Println("Is safe to be stack-allocated?", esc)
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
		fmt.Println()

	} else {
		// Else we need to check each reference to value v. We're doing this by
		// means of a DFS-like algorithm that may stop if we found a
		// "mustEscape" value.
		for _, ref := range node.references {
			analyzeNode(node, ref)
			fmt.Println()

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
	fmt.Println("ANALYZE LEAF")
	fmt.Println(node.value.LongString())

	switch node.value.Op {
	case OpStore:
		gcnode, ok := node.value.Args[0].Aux.(GCNode)
		if !(ok && gcnode.StorageClass() == ClassParamOut) {
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
	fmt.Println("ANALYZE NODE")
	fmt.Println(node.value.LongString())
	fmt.Println(ref.value.LongString())

	switch ref.value.Op {
	case OpStore:
		fmt.Println("STORE")

		// We only care for write operations, so to v escapes it first needs to
		// be being written to another value (i.e. appears as Args[1]).
		if node.value != ref.value.Args[1] {
			node.kind = safe
			return
		}

		fmt.Println(ref.value.Args[0].LongString())
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
		fmt.Println("COPY")
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
