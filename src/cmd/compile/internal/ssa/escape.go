// Copyright 2019 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

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

// escapes walks through the values of a function f to determine whether
// a value can safely be stack-allocated or it really escapes to the heap. This
// complements the escape analysis applied to the AST.
func escapes(f *Func) {
	// TODO: REMOVE!!!!!
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

			var load *Value

			// There's no guarantee that the OpLoad will be the first
			// reference.
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

			newobjList = append(newobjList, newobj)
			root := refmap[newobj.ret.load]
			dfs(root)

			// TODO: REMOVE!!!!!
			esc := root.state == safe
			log.Printf("%s: is %s safe to be stack-allocated? %t", f.Name, newobj.ret.load.LongString(), esc)
		}
	}

	for _, n := range newobjList {
		if refmap[n.ret.load].state == safe {
			sp := n.call.offptr.Args[0]

			// GCNode of the new stack-allocated var.
			pos := n.ret.load.Pos
			typ := n.ret.load.Type.Elem()
			node := f.Frontend().Auto(pos, typ)

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
			s := unchecked
			if outlives(v) {
				s = mayEscape
			}

			refmap[v] = &escapeNode{
				value:      v,
				state:      s,
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

				outlivesArg(refmap[v], refmap[arg])
			}
		}
	}

	return refmap
}

// Check if v is somehow (arg) related to a global value or param/paramout.
func outlivesArg(node, arg *escapeNode) {
	v, a := node.value, arg.value
	if arg.state == mustEscape || isWriteOp(v) && a == v.Args[0] && outlives(a) {
		node.state = mustEscape
	}
}

// Check if v is related to a global value or param/paramout.
func outlives(v *Value) bool {
	// OpAddr means that v is global.
	if v.Op == OpAddr {
		return true
	}

	// Value is param/paramout.
	if n, ok := v.Aux.(GCNode); ok && n.StorageClass() != ClassAuto {
		return n.Typ().IsPtr() || n.Typ().IsUnsafePtr()
	}

	return false
}

func isWriteOp(v *Value) bool {
	// TODO: there's any other OP with write semantics?
	switch v.Op {
	case OpStore, OpMove, OpZero, OpStoreWB, OpMoveWB, OpZeroWB:
		return true
	default:
		return false
	}
}

func isDead(v *Value) bool {
	return v.Uses == 0
}

func dfs(root *escapeNode) {
	// Create new queue and visited map for running dfs.
	stack := []*escapeNode{root}
	visited := map[*escapeNode]bool{}

	for len(stack) > 0 {
		// Pop the first element from the stack.
		var node *escapeNode
		node, stack = stack[len(stack)-1], stack[:len(stack)-1]

		if visited[node] {
			continue
		}

		visited[node] = true

		// Already established that root must escape.
		if root.state == mustEscape || node.state == mustEscape {
			root.state = mustEscape
			break
		}

		if len(node.references) == 0 {
			checkNode(node)

		} else {
			// Add node children to the stack.
			stack = append(stack, node.references...)

			// Set the child as the first node in the stack and visit.
			child := stack[len(stack)-1]
			walk(node, child)
		}

		if node.state != mayEscape {
			root.state = node.state
		}
	}
}

// visit is called when node doesn't have any children, so there's no
// reason to return "mayEscape".
func checkNode(node *escapeNode) {
	if node.value.Op.IsCall() {
		// TODO: There's any way to handle it?
		node.state = mustEscape
		return
	}

	if !isWriteOp(node.value) {
		node.state = safe
		return
	}

	// TODO: Cover more cases!!!!!
	if node.state = checkType(node.value, true); node.state == mayEscape {
		node.state = mustEscape
	}
}

// Check if there's any chance of a value v to escape from the function considering
// a reference to v.
func walk(node, child *escapeNode) {
	if child.value.Op.IsCall() {
		// TODO: There's any way to handle it?
		node.state = mustEscape
		return
	}

	// Look-ahead by checking the child value.
	// TODO: Cover more cases!!!!!
	node.state = checkType(child.value, false)
}

func checkType(v *Value, memsafe bool) nodeState {
	if typ := v.Type; typ.HasNil() || (typ.IsMemory() && !memsafe) {
		return mayEscape
	}

	return safe
}
