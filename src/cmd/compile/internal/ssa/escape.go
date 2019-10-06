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

			// There's no guarantee that the OpLoad will be the first reference
			// so we need to run through the list.
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
			bfs(root)

			// TODO: REMOVE!!!!!
			esc := root.state == safe
			log.Printf("%s: is %s safe to be stack-allocated? %t", f.Name, newobj.ret.load, esc)
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
			refmap[v] = &escapeNode{
				value:      v,
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

func isDead(v *Value) bool {
	return v.Uses == 0
}

func bfs(root *escapeNode) {
	// Create new queue and visited map for running bfs.
	queue := []*escapeNode{root}
	visited := map[*escapeNode]bool{}
	visited[root] = true

	for len(queue) > 0 {
		// Get the first element of the queue.
		var node *escapeNode
		node, queue = queue[0], queue[1:]

		// If node was already visited we only need to analyze it if its state
		// is not a final state (safe or mustEscape).
		if node.state == mustEscape {
			break
		}

		if node.state == safe {
			continue
		}

		if len(node.references) == 0 {
			visitNode(node)
			root.state = node.state

			// TODO: REMOVE!!!!!
			// log.Println(node.value.LongString())
			// log.Println(root.state)
			// fmt.Println()

			if root.state == mustEscape {
				break
			}

			continue
		}

		// Else we need to check each reference to value v. Edges will be
		// cutted if we found a "mustEscape" value.
		for _, child := range node.references {
			if visited[child] {
				continue
			}

			visitChild(node, child)
			visited[child] = true
			root.state = node.state

			// TODO: REMOVE!!!!!
			// log.Println(node.value.LongString())
			// log.Println(child.value.LongString())
			// log.Println(root.state)
			// fmt.Println()

			if root.state == mayEscape {
				queue = append(queue, child)
			}

			if root.state == mustEscape {
				queue = nil
				break
			}
		}
	}
}

// visitNode is called when node doesn't have any children, so there's no
// reason to return "mayEscape".
func visitNode(node *escapeNode) {
	switch node.value.Op {
	case OpStore:
		if !node.value.Args[1].Type.IsPtr() {
			node.state = safe
			return
		}

		gcnode, ok := node.value.Args[0].Aux.(GCNode)

		// If Args[0] class is ParamOut and the value being returned (Args[1])
		// is an address, thus the root node must escape for sure. Else, we
		// can guarantee the safety since curent node has no child.
		if ok && gcnode.StorageClass() == ClassParamOut {
			node.state = mustEscape
			return
		}
	}

	// Default value for visitNode.
	node.state = safe
}

// Check if there's any chance to a value escapes from the function considering
// a reference to v.
func visitChild(node, child *escapeNode) {

	if child.value.Op.IsCall() {
		// TODO: There's any way to handle it?
		node.state = mustEscape
		return
	}

	switch child.value.Op {
	case OpStore:
		// We only care for read ops (i.e. node.value at args[1]) where the
		// type is a ptr to something.
		if !isRead(child.value, node.value) {
			node.state = safe
			return
		}

		rarg := child.value.Args[1]
		if !rarg.Type.IsPtr() && !rarg.Type.IsUnsafePtr() {
			node.state = safe
			return
		}

		// If Args[0] class is ParamOut and the value being returned (Args[1])
		// is an address, thus the root node must escape for sure. Else, we
		// cannot guarantee the safety.
		gcnode, ok := child.value.Args[0].Aux.(GCNode)
		if ok && gcnode.StorageClass() == ClassParamOut {
			node.state = mustEscape
		}

	case OpLoad:
		// If the returned type of OpLoad is a pointer, than it may be being
		// used for something like a return or assignment to a global variable.
		// Else, we can guarantee the safety.
		if !child.value.Type.IsPtr() || !child.value.Type.IsUnsafePtr() {
			node.state = safe
			return
		}
	}

	// Default value for visitChild.
	node.state = mayEscape
}
