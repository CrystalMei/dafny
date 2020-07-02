newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i < 0x1_0000_0000_0000_0000

datatype Option<V> = None | Some(value:V) 
type AbInt(==)
function method int2adt (n: int) : (r: AbInt)
predicate AbIsZero (n: AbInt) {n == int2adt(0)}
predicate AbNonNeg (n: AbInt) { true }
predicate AbPos (n: AbInt) {AbNonNeg(n) && !AbIsZero(n)}

function method AbLt(n: AbInt, m: AbInt) : bool
function method AbAdd(n: AbInt, m: AbInt) : (r: AbInt)
function method AbSub(n: AbInt, m: AbInt) : (r: AbInt)
lemma Props_plus_and_minus ()
  ensures forall x, y, z :: AbAdd(x, y) == z ==> AbSub(z, y) == x && AbSub(z, x) == y

function method seq_get<A>(s:seq<A>, i:uint64):(a:A)
  requires i as int < |s|
  ensures a == s[i] 

function method seq_set<A>(s1:seq<A>, i:uint64, a:A):(s2:seq<A>) // can be implemented as in-place update
  requires i as nat < |s1|
  ensures s2 == s1[i as nat := a] 

datatype Node<A> = Node(data:Option<A>, next:uint64, prev:uint64)
datatype DList<A> = DList(
  nodes:seq<Node<A>>, // sequence of nodes held by the list, indexed by pointer p
  freeStack:uint64, // pointer to singly-linked stack of free nodes
  ghost s:seq<A>, // sequence of data values held by the list, indexed by integer index i
  ghost f:seq<int>, // map index to pointer: f[i] = p (where p > 0)
  ghost g:seq<int>  // map pointer to index: g[p] = i (where g[p] == -2 means p is unused and g[0] == -1 (sentinel))
  )

ghost const unused:int := -2
ghost const sentinel:int := -1

// make sure the list-seq mapping is correct.
predicate Invs<A>(nodes:seq<Node<A>>, freeStack:uint64, s:seq<A>, f:seq<int>, g:seq<int>)
{
  && |f| == |s|
  && |g| == |nodes|
  && |nodes| > 0
  && g[0] == sentinel
  && 0 <= freeStack as int < |nodes|
  && (forall i :: 0 <= i < |f| ==> 0 < f[i] < |nodes|)
  && (forall i {:trigger g[f[i]]} :: 0 <= i < |f| ==> g[f[i]] == i)
  && (forall p :: 0 <= p < |g| ==>
    && unused <= g[p] < |s|
    && 0 <= nodes[p].next as int < |g|
    && (g[p] >= 0 <==> nodes[p].data.Some?))
  && (forall p :: 0 <= p < |g| && sentinel <= g[p] ==>
    && (g[p] == sentinel ==> p == 0)
    && (0 <= g[p] ==> f[g[p]] == p && nodes[p].data == Some(s[g[p]]))
    && nodes[p].next as int == (
      if g[p] + 1 < |f| then f[g[p] + 1] // nonlast.next or sentinel.next
      else 0) // last.next == sentinel or sentinel.next == sentinel
    && nodes[p].prev as int == (
      if g[p] > 0 then f[g[p] - 1] // nonfirst.prev
      else if g[p] == 0 || |f| == 0 then 0 // first.prev == sentinel or sentinel.prev == sentinel
      else f[|f| - 1]) // sentinel.prev == last
    )
}
predicate Inv<A>(l:DList<A>)
{
  Invs(l.nodes, l.freeStack, l.s, l.f, l.g)
}

function Seq<A>(l:DList<A>):seq<A>
{
  l.s
}

function ValidPtr<A>(l:DList<A>, p:uint64):(b:bool)
  ensures b ==> p != 0
{
  0 < p as int < |l.g| && l.g[p] >= 0
}
 
predicate MaybePtr<A>(l:DList<A>, p:uint64)
{
  p == 0 || ValidPtr(l, p)
}
 
function Index<A>(l:DList<A>, p:uint64):(i:int)
  ensures Inv(l) && ValidPtr(l, p) ==> 0 <= i < |Seq(l)|
  ensures Inv(l) && p == 0 ==> i == -1
{
  if Inv(l) && MaybePtr(l, p) then l.g[p] else 0
}
 
// Remove from dlist and seq
// ~1s
method Remove<A>(l:DList<A>, p:uint64) returns(l':DList<A>)
  requires Inv(l)
  requires ValidPtr(l, p)
  ensures Inv(l')
  ensures Seq(l') == Seq(l)[.. Index(l, p)] + Seq(l)[Index(l, p) + 1 ..]
  ensures forall x :: x != p && ValidPtr(l, x) ==>
    ValidPtr(l', x) && Index(l', x) == Index(l, x) - (if Index(l, x) < Index(l, p) then 0 else 1)
{
  var DList(nodes, freeStack, s, f, g) := l;
  ghost var index := g[p];
  ghost var s' := RemoveIdx(index, s); // s[.. index] + s[index + 1 ..];
  ghost var f' := RemoveIdx(index, f); // f[.. index] + f[index + 1 ..];
  ghost var g' := seq(|g|, x requires 0 <= x < |g| =>
    if g[x] == index then unused else if g[x] > index then g[x] - 1 else g[x]);
  var node := seq_get(nodes, p);
  var node_prev := seq_get(nodes, node.prev);
  nodes := seq_set(nodes, node.prev, node_prev.(next := node.next));
  var node_next := seq_get(nodes, node.next);
  nodes := seq_set(nodes, node.next, node_next.(prev := node.prev));
  nodes := seq_set(nodes, p, Node(None, freeStack, 0));
  l' := DList(nodes, p, s', f', g');
}

function method RemoveIdx<A> (i: int, s: seq<A>) :(s': seq<A>)
  requires 0 <= i < |s|
  ensures |s| == |s'| + 1
  ensures forall x :: 0 <= x < i ==> s[x] == s'[x]
  ensures forall x :: i < x < |s'| ==> s[x+1] == s'[x] 
{
  s[.. i] + s[i + 1 ..]
}

// function method {:extern "LinearExtern", "seq_length"} seq_length<A>(s:seq<A>):(n:uint64)
//   requires |s| <= 0xffff_ffff_ffff_ffff
//   ensures n as int == |s| 

// function method {:extern "LinearExtern", "seq_empty"} seq_empty<A>():(s:seq<A>)
//   ensures |s| == 0 

// function method {:extern "LinearExtern", "seq_alloc"} seq_alloc<A>(length:uint64, a:A):(s:seq<A>)
//   ensures |s| == length as int
//   ensures forall i :: 0 <= i < |s| ==> s[i] == a 

// function method {:extern "LinearExtern", "seq_free"} seq_free<A>(s:seq<A>):() 

// function method {:extern "LinearExtern", "seq_unleash"} seq_unleash<A>(s1:seq<A>):(s2:seq<A>)
//     ensures s1 == s2 

// // must be a method, not a function method, so that we know s is a run-time value, not a ghost value
// method {:extern "LinearExtern", "seq_length_bound"} seq_length_bound<A>(s:seq<A>)
//   ensures |s| < 0xffff_ffff_ffff_ffff 

// must be a method, not a function method, so that we know s is a run-time value, not a ghost value

// method {:extern "LinearExtern", "shared_seq_length_bound"} shared_seq_length_bound<A>(s:seq<A>)
//   ensures |s| < 0xffff_ffff_ffff_ffff 

// method SeqResize<A>(s: seq<A>, newlen: uint64, a: A) returns (s2: seq<A>)
//   ensures |s2| == newlen as nat
//   ensures forall j :: 0 <= j < newlen as nat ==> s2[j] == (if j < |s| then s[j] else a) 

// method AllocAndCopy<A>(source: seq<A>, from: uint64, to: uint64)
//   returns (dest: seq<A>)
//   requires 0 <= from as nat <= to as nat <= |source|;
//   ensures source[from..to] == dest

/*
A DList<A> is a doubly-linked list that represents a sequence s of type seq<A>.
It supports efficient insertion and removal but not efficient indexing.
A pointer p of type int is a pointer to a node in the list.
The DList is implemented as a mutable sequence of nodes, where nodes[0] is a sentinel.
*/
// integer: position in seq: index
// integer: position in dlist: pointer

// function IndexHi<A>(l:DList<A>, p:uint64):(i:int)
//   ensures Inv(l) && ValidPtr(l, p) ==> i == Index(l, p)
//   ensures Inv(l) && p == 0 ==> i == |Seq(l)|
// {
//   if Inv(l) && ValidPtr(l, p) then l.g[p] else |l.s|
// }
 
// function method Get<A>(l:DList<A>, p:uint64):(a:A)
//   requires Inv(l)
//   requires ValidPtr(l, p)
//   ensures a == Seq(l)[Index(l, p)]
// {
//   seq_get(l.nodes, p).data.value
// }
 
// function method Next<A>(l:DList<A>, p:uint64):(p':uint64)
//   requires Inv(l)
//   requires MaybePtr(l, p)
//   ensures MaybePtr(l, p')
//   ensures p == 0 && |Seq(l)| > 0 ==> Index(l, p') == 0
//   ensures p == 0 && |Seq(l)| == 0 ==> p' == 0
//   ensures p != 0 && Index(l, p) + 1 < |Seq(l)| ==> Index(l, p') == Index(l, p) + 1
//   ensures p != 0 && Index(l, p) + 1 == |Seq(l)| ==> p' == 0
// {
//   seq_get(l.nodes, p).next
// }
 
// function method Prev<A>(l:DList<A>, p:uint64):(p':uint64)
//   requires Inv(l)
//   requires MaybePtr(l, p)
//   ensures MaybePtr(l, p')
//   ensures p == 0 && |Seq(l)| > 0 ==> Index(l, p') == |Seq(l)| - 1
//   ensures p == 0 && |Seq(l)| == 0 ==> p' == 0
//   ensures p != 0 && Index(l, p) > 0 ==> Index(l, p') == Index(l, p) - 1
//   ensures p != 0 && Index(l, p) == 0 == |Seq(l)| ==> p' == 0
// {
//   seq_get(l.nodes, p).prev
// }
 
// method BuildFreeStack<A>(a:seq<Node<A>>, k:uint64) returns(b:seq<Node<A>>)
//   requires 0 < k as nat <= |a|
//   ensures |b| == |a|
//   ensures forall i :: 0 <= i < k as nat ==> b[i] == a[i]
//   ensures forall i :: k as nat <= i < |a| <= 0xffff_ffff_ffff_ffff ==> b[i] == Node(None, i as uint64 - 1, 0)
// {
//   b := a;
//   var n := k;
//   shared_seq_length_bound(b);
//   while (n < seq_length(b))
//     invariant k as int <= n as int <= |b|
//     invariant |b| == |a|
//     invariant forall i :: 0 <= i < k as nat ==> b[i] == a[i]
//     invariant forall i :: k as nat <= i < n as nat ==> b[i] == Node(None, i as uint64 - 1, 0)
//   {
//     b := seq_set(b, n, Node(None, n - 1, 0));
//     n := n + 1;
//   }
// }

// // initial_len should be the initial capacity plus 1
// method Alloc<A>(initial_len:uint64) returns(l:DList<A>)
//   requires initial_len > 0
//   ensures Inv(l)
//   ensures Seq(l) == []
// {
//   var nodes := seq_alloc<Node>(initial_len, Node(None, 0, 0));
//   nodes := BuildFreeStack(nodes, 1);
//   l := DList(nodes, initial_len - 1, [], [], seq(initial_len as nat, p => if p == 0 then sentinel else unused));
// }

// method Free<A>(l:DList<A>)
// {
//   var DList(nodes, freeStack, s, f, g) := l;
//   var _ := seq_free(nodes);
// }

// method Expand<A>(l:DList<A>) returns(l':DList<A>)
//   requires Inv(l)
//   ensures Inv(l')
//   ensures l'.s == l.s
//   ensures forall x :: ValidPtr(l, x) ==> ValidPtr(l', x) && l'.g[x] == l.g[x]
//   ensures l'.freeStack != 0 && l'.nodes[l'.freeStack].data.None?
// {
//   var DList(nodes, freeStack, s, f, g) := l;
//   shared_seq_length_bound(nodes);
//   var len := seq_length(nodes);
//   shared_seq_length_bound(nodes);
//   var len' := if len < 0x7fff_ffff_ffff_ffff then len + len else len + 1;
//   nodes := SeqResize(nodes, len', Node(None, freeStack, 0));
//   nodes := BuildFreeStack(nodes, len + 1);
//   l' := DList(nodes, len' - 1, s, f, seq(|nodes|,
//     i requires 0 <= i < |nodes| => if i < |g| then g[i] else unused));
// }

// // ~8s
// method InsertAfter<A>(l:DList<A>, p:uint64, a:A) returns(l':DList<A>, p':uint64)
//   requires Inv(l)
//   requires MaybePtr(l, p)
//   ensures Inv(l')
//   ensures Seq(l') == Seq(l)[.. Index(l, p) + 1] + [a] + Seq(l)[Index(l, p) + 1 ..]
//   ensures ValidPtr(l', p') && Index(l', p') == Index(l, p) + 1
//   ensures forall x :: ValidPtr(l, x) ==>
//     ValidPtr(l', x) && Index(l', x) == Index(l, x) + (if Index(l, x) <= Index(l, p) then 0 else 1)
// {
//   l' := l;
//   p' := l'.freeStack;
//   var freeNode := seq_get(l'.nodes, p');
//   if (p' == 0 || freeNode.data.Some?) {
//     l' := Expand(l');
//     p' := l'.freeStack;
//     freeNode := seq_get(l'.nodes, p');
//   }
//   var DList(nodes, freeStack, s, f, g) := l';
//   ghost var index := g[p];
//   ghost var index' := index + 1;
//   ghost var s' := s[.. index'] + [a] + s[index' ..];
//   ghost var f' := f[.. index'] + [p' as int] + f[index' ..];
//   ghost var g' := seq(|g|, x requires 0 <= x < |g| =>
//     if x == p' as int then index' else if g[x] > index then g[x] + 1 else g[x]);
//   var node := seq_get(nodes, p);
//   var node' := Node(Some(a), node.next, p);
//   nodes := seq_set(nodes, p, node.(next := p'));
//   var node_next := seq_get(nodes, node.next);
//   nodes := seq_set(nodes, node.next, node_next.(prev := p'));
//   nodes := seq_set(nodes, p', node');
//   l' := DList(nodes, freeNode.next, s', f', g');
// }
 
// // ~ 13s
// method InsertBefore<A>(l:DList<A>, p:uint64, a:A) returns(l':DList<A>, p':uint64)
//   requires Inv(l)
//   requires MaybePtr(l, p)
//   ensures Inv(l')
//   ensures Seq(l') == Seq(l)[.. IndexHi(l, p)] + [a] + Seq(l)[IndexHi(l, p) ..]
//   ensures ValidPtr(l', p') && Index(l', p') == IndexHi(l, p)
//   ensures forall x :: ValidPtr(l, x) ==>
//     ValidPtr(l', x) && Index(l', x) == Index(l, x) + (if Index(l, x) < IndexHi(l, p) then 0 else 1)
// {
//   l' := l;
//   p' := l'.freeStack;
//   var freeNode := seq_get(l'.nodes, p');
//   if (p' == 0 || freeNode.data.Some?) {
//     l' := Expand(l');
//     p' := l'.freeStack;
//     freeNode := seq_get(l'.nodes, p');
//   }
//   var DList(nodes, freeStack, s, f, g) := l';
//   ghost var index' := IndexHi(l, p);
//   ghost var s' := s[.. index'] + [a] + s[index' ..];
//   ghost var f' := f[.. index'] + [p' as int] + f[index' ..];
//   ghost var g' := seq(|g|, x requires 0 <= x < |g| =>
//     if x == p' as int then index' else if g[x] >= index' then g[x] + 1 else g[x]);
//   var node := seq_get(nodes, p);
//   var node' := Node(Some(a), p, node.prev);
//   nodes := seq_set(nodes, p, node.(prev := p'));
//   var node_prev := seq_get(nodes, node.prev);
//   nodes := seq_set(nodes, node.prev, node_prev.(next := p'));
//   nodes := seq_set(nodes, p', node');
//   l' := DList(nodes, freeNode.next, s', f', g');
// }

// method Clone<A>(l:DList<A>) returns(l':DList<A>)
//   ensures l' == l
// {
//   var DList(nodes, freeStack, s, f, g) := l;
//   shared_seq_length_bound(nodes);
//   var nodes' := AllocAndCopy(nodes, 0, seq_length(nodes));
//   l' := DList(nodes', freeStack, s, f, g);
// }

// // ~ 1500s
// method main()
// {
//   var l := Alloc<uint64>(3);
//   var p;
//   l, p := InsertAfter(l, 0, 100);
//   l, p := InsertAfter(l, p, 200);
//   l, p := InsertAfter(l, p, 300);
//   var p3 := p;
//   l, p := InsertAfter(l, p, 400);
//   l, p := InsertAfter(l, p, 500);
//   assert Seq(l) == [100, 200, 300, 400, 500];
//   l := Remove(l, p3);
//   assert Seq(l) == [100, 200, 400, 500];
//   l, p := InsertAfter(l, p, 600);
//   l, p := InsertAfter(l, p, 700);
//   assert Seq(l) == [100, 200, 400, 500, 600, 700];
//   Free(l);
// }
