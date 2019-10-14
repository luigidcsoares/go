// Copyright 2019 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"cmd/compile/internal/types"
	"cmd/internal/obj"
	"fmt"
	"strings"
	"sync"
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
		region     nodeRegion
		state      nodeState
		references []*escapeNode
	}

	nodeState  = uint8
	nodeRegion = uint8
)

const (
	safe nodeState = iota
	mayEscape
	mustEscape
)

const (
	inside nodeRegion = iota
	outside
)

// escapes walks through the values of a function f to determine whether
// a value can safely be stack-allocated or it really escapes to the heap. This
// complements the escape analysis applied to the AST.
func escapes(f *Func) {
	if f.Name != "foo" {
		return
	}

	// Init refmap to keep track of each reference to a value.
	refmap := findRefs(f)
	setRegion(refmap)

	// Keep track of each heap allocation to rewrite later.
	rewriteList := []newobject{}

	// Lookup for calls to runtime.newobject (i.e. heap allocations).
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			if !isNewobjCall(v) {
				continue
			}

			var load *Value
			for _, r := range refmap[v].references {
				if r.value.Op == OpLoad {
					load = r.value
					break
				}
			}

			newobj := newobject{
				call: newobjectCall{
					addr:       v.Args[0].Args[1],
					offptr:     v.Args[0].Args[0],
					store:      v.Args[0],
					staticcall: v,
				},
				ret: newobjectRet{
					offptr: load.Args[0],
					load:   load,
				},
			}

			root := refmap[newobj.ret.load]
			walk(root, refmap)

			if root.state == safe {
				rewriteList = append(rewriteList, newobj)
				fmt.Println(newobj.ret.load.LongString())
			}
		}
	}

	for _, n := range rewriteList {
		sp := n.call.offptr.Args[0]

		// GCNode of the new stack-allocated var.
		pos := n.ret.load.Pos
		t := n.ret.load.Type.Elem()
		node := f.Frontend().Auto(pos, t)

		// Reuse staticcall as the new vardef value.
		n.call.staticcall.reset(OpVarDef)
		n.call.staticcall.Pos = pos
		n.call.staticcall.Type = types.TypeMem
		n.call.staticcall.AddArg(n.call.store.MemoryArg())
		n.call.staticcall.Aux = node

		// Reset the remaining heap-alloc values.
		n.call.store.reset(OpInvalid)
		n.call.addr.reset(OpInvalid)

		if isDead(n.call.offptr) {
			n.call.offptr.reset(OpInvalid)
		}

		if isDead(n.ret.offptr) {
			n.ret.offptr.reset(OpInvalid)
		}

		n.ret.load.reset(OpLocalAddr)
		n.ret.load.AddArgs(sp, n.call.staticcall)
		n.ret.load.Aux = node
	}
}

func isDead(v *Value) bool {
	return v.Uses == 0
}

func isNewobjCall(v *Value) bool {
	switch aux := v.Aux.(type) {
	case *obj.LSym:
		return v.Op == OpStaticCall &&
			isSameSym(aux, "runtime.newobject")
	default:
		return false
	}
}

func isTypeAddr(v *Value) bool {
	switch aux := v.Aux.(type) {
	case *obj.LSym:
		return strings.Contains(aux.Name, "type.")
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
			r := inside

			if v.Op == OpAddr && !isTypeAddr(v) {
				// Global value.
				r = outside
			}

			n, ok := v.Aux.(GCNode)
			if !v.Type.IsMemory() && ok && n.StorageClass() != ClassAuto {
				// Param (in/out).
				r = outside
			}

			refmap[v] = &escapeNode{
				value:      v,
				region:     r,
				state:      mayEscape,
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

// Each entry of refmap can be thought as a directed graph where each arg of a
// value v is onde node that connected to v. So, we run a DFS algorithm to
// propagate the region of a parent node to its children, but must only update
// outside regions.
func setRegion(refmap map[*Value]*escapeNode) {
	var wg sync.WaitGroup

	for _, node := range refmap {
		if node.region == inside {
			continue
		}

		wg.Add(1)
		go func(node *escapeNode) {
			defer wg.Done()
			stack := []*escapeNode{}
			visited := map[*escapeNode]bool{}

			stack = append(stack, node.references...)
			parent := node

			for len(stack) > 0 {
				var child *escapeNode
				child, stack = stack[len(stack)-1], stack[:len(stack)-1]

				// If child region is outside, let the child propagate its
				// region.
				if child.region == outside {
					break
				}

				if visited[child] {
					continue
				}

				if parent.region == outside {
					child.region = outside
				}

				visited[child] = true
				stack = append(stack, child.references...)
				parent = child
			}
		}(node)
	}

	wg.Wait()
}

func walk(root *escapeNode, refmap map[*Value]*escapeNode) {
	stack := []*escapeNode{}
	visited := map[*escapeNode]bool{}

	stack = append(stack, root.references...)
	for len(stack) > 0 {
		var node *escapeNode
		node, stack = stack[len(stack)-1], stack[:len(stack)-1]

		if visited[node] {
			continue
		}

		visit(node, refmap)
		visited[node] = true

		if node.state == mustEscape {
			root.state = mustEscape
			break
		}

		// If node.state is safe, then there's no reason to visit its children.
		if node.state == safe {
			root.state = safe
			continue
		}

		stack = append(stack, node.references...)
	}
}

func visit(node *escapeNode, refmap map[*Value]*escapeNode) {
	if node.value.Op.IsCall() {
		// TODO: there's any way to handle it?
		node.state = mustEscape
		return
	}

	node.state = checkHeapPointer(node.value)
	if node.state == mustEscape {
		return
	}

	// TODO: there's any other OP with write semantics?
	switch node.value.Op {
	case OpStore, OpMove:
		src, dst := node.value.Args[1], node.value.Args[0]

		if !types.Haspointers(src.Type) {
			node.state = safe
			return
		}

		node.state = checkHeapPointer(src)
		if node.state == mustEscape {
			return
		}

		// Assigning address to a value that is outside of the curr fn.
		if refmap[dst].region == outside {
			node.state = mustEscape
			return
		}

		node.state = mayEscape

	default:
		if t := node.value.Type; !types.Haspointers(t) && !t.IsMemory() {
			node.state = safe
		}
	}
}

func checkHeapPointer(v *Value) (state nodeState) {
	state = mayEscape
	elem := v.Type

	for elem.IsPtr() {
		elem = elem.Elem()
	}

	if elem.HasHeapPointer() {
		// v has some pointer to heap so we consider it as being
		// outside of the curr fn.
		// TODO: Try to relax this constraint a bit.
		state = mustEscape
	}

	return
}
