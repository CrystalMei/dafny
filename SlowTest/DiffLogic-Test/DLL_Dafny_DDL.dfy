function method Dec(a: int, b: int) : int
lemma Props_dec_one (sum: int)
    ensures forall j: int :: Dec(sum, j + 1) < Dec(sum, j)
lemma Props_dec_lower_bound (sum: int, x: int)
    requires x <= sum
    ensures 0 <= Dec(sum, x)

function method Add(a: int, b: int): int { a + b }
function method Sub(a: int, b: int): int { a - b }

function method SeqRemove<X> (s: seq<X>, k: int) : (s': seq<X>)
  requires 0 <= k < |s|
  ensures Sub(|s|, 1) == |s'|
  ensures forall i: int {:trigger s'[i]} :: 0 <= i < |s'| ==>
    if i < k then s'[i] == s[i]
    else s'[i] == s[Add(i, 1)]

function method SeqInsert<X> (s: seq<X>, k: int, v: X) : (s': seq<X>)
  requires 0 <= k <= |s|
  ensures |s'| == Add(|s|, 1)
  ensures forall i: int {:trigger s'[i]} :: 0 <= i < |s'| ==>
    if i < k then s'[i] == s[i]
    else if i == k then s'[i] == v
    else s'[i] == s[Sub(i, 1)]

function method SeqInit<X> (len: int, func : int --> X) : (s: seq<X>)
  requires len >= 0
  requires forall i : int :: 0 <= i < len ==> func.requires(i)
  ensures |s| == len
  ensures forall i : int {:trigger s[i]} :: 0 <= i < len ==> s[i] == func(i)

datatype Option<V> = None | Some(value:V) 

function method seq_get<A>(s:seq<A>, i:int):(a:A)
  requires 0 <= i < |s|
  ensures a == s[i] 

function method seq_set<A>(s1:seq<A>, i:int, a:A):(s2:seq<A>)
  requires 0 <= i < |s1|
  ensures s2 == s1[i := a] 

function method {:extern "LinearExtern", "seq_length"} seq_length<A>(s:seq<A>):(n:int)
  ensures n == |s| 

function method {:extern "LinearExtern", "seq_empty"} seq_empty<A>():(s:seq<A>)
  ensures |s| == 0 

function method {:extern "LinearExtern", "seq_alloc"} seq_alloc<A>(length:int, a:A):(s:seq<A>)
  ensures |s| == length
  ensures forall i: int {:trigger s[i]} :: 0 <= i < |s| ==> s[i] == a 

function method {:extern "LinearExtern", "seq_free"} seq_free<A>(s:seq<A>):() 

function method {:extern "LinearExtern", "seq_unleash"} seq_unleash<A>(s1:seq<A>):(s2:seq<A>)
    ensures s1 == s2 

method SeqResize<A>(s: seq<A>, newlen: int, a: A) returns (s2: seq<A>)
  ensures |s2| == newlen
  ensures forall j: int {:trigger s2[j]} :: 0 <= j < newlen ==> s2[j] == (if j < |s| then s[j] else a) 

method AllocAndCopy<A>(source: seq<A>, from: int, to: int)
  returns (dest: seq<A>)
  requires 0 <= from <= to <= |source|;
  ensures source[from..to] == dest

/*
A DList<A> is a doubly-linked list that represents a sequence s of type seq<A>.
It supports efficient insertion and removal but not efficient indexing.
A pointer p of type int is a pointer to a node in the list.
The DList is implemented as a mutable sequence of nodes, where nodes[0] is a sentinel.
*/
// integer: position in seq: index
// integer: position in dlist: pointer

datatype Node<A> = Node(data:Option<A>, next:int, prev:int)
datatype DList<A> = DList(
  nodes:seq<Node<A>>, // sequence of nodes held by the list, indexed by pointer p
  freeStack:int, // pointer to singly-linked stack of free nodes
  ghost s:seq<A>, // sequence of data values held by the list, indexed by integer index i
  ghost f:seq<int>, // map index to pointer: f[i] = p (where p > 0)
  ghost g:seq<int>  // map pointer to index: g[p] = i (where g[p] == -2 means p is unused and g[0] == -1 (sentinel))
  )

ghost const unused:int := -2
ghost const sentinel:int := -1

// make sure the list-seq mapping is correct.
predicate Invs<A>(nodes:seq<Node<A>>, freeStack:int, s:seq<A>, f:seq<int>, g:seq<int>)
{
  && |f| == |s|
  && |g| == |nodes|
  && |nodes| > 0
  && g[0] == sentinel
  && 0 <= freeStack < |nodes|
  && (forall i: int {:trigger f[i]} :: 0 <= i < |f| ==> 0 < f[i] < |nodes|)
  && (forall i: int {:trigger g[f[i]]} :: 0 <= i < |f| ==> g[f[i]] == i)
  && (forall p: int {:trigger g[p]} :: 
    0 <= p < |g| ==> unused <= g[p] < |s| )
  && (forall p: int {: trigger nodes[p]} :: 
    0 <= p < |g| ==> 0 <= nodes[p].next < |g| )
  && (forall p: int {:trigger g[p]} {: trigger nodes[p]} :: 
    0 <= p < |g| ==> (g[p] >= 0 <==> nodes[p].data.Some?) )
  && (forall p: int {:trigger g[p]} :: 
    0 <= p < |g| && sentinel <= g[p] ==> (g[p] == sentinel ==> p == 0) )
  && (forall p: int {:trigger g[p]} {:trigger f[g[p]]} {:trigger s[g[p]]} :: 
    0 <= p < |g| && sentinel <= g[p] ==>
      (0 <= g[p] ==> f[g[p]] == p && nodes[p].data == Some(s[g[p]])) )
  && (forall p: int {:trigger g[p]} {:trigger nodes[p].next} ::
    0 <= p < |g| && sentinel <= g[p] ==>
      nodes[p].next == (
        if Add(g[p], 1) < |f| then f[Add(g[p], 1)] // nonlast.next or sentinel.next
        else 0) ) // last.next == sentinel or sentinel.next == sentinel
  && (forall p: int {:trigger g[p]} {:trigger nodes[p].prev} ::
    0 <= p < |g| && sentinel <= g[p] ==>
    && nodes[p].prev == (
      if g[p] > 0 then f[Sub(g[p], 1)] // nonfirst.prev
      else if g[p] == 0 || |f| == 0 then 0 // first.prev == sentinel or sentinel.prev == sentinel
      else f[Sub(|f|, 1)]) ) // sentinel.prev == last
}

predicate Inv<A>(l:DList<A>)
{
  Invs(l.nodes, l.freeStack, l.s, l.f, l.g)
}

function Seq<A>(l:DList<A>):seq<A>
{
  l.s
}

function ValidPtr<A>(l:DList<A>, p:int):(b:bool)
  ensures b ==> p != 0
{
  0 < p < |l.g| && l.g[p] >= 0
}
 
predicate MaybePtr<A>(l:DList<A>, p:int)
{
  p == 0 || ValidPtr(l, p)
}
 
function Index<A>(l:DList<A>, p:int):(i:int)
  ensures Inv(l) && ValidPtr(l, p) ==> 0 <= i < |Seq(l)|
  ensures Inv(l) && p == 0 ==> i == -1
{
  if Inv(l) && MaybePtr(l, p) then l.g[p] else 0
}
 
function IndexHi<A>(l:DList<A>, p:int):(i:int)
  ensures Inv(l) && ValidPtr(l, p) ==> i == Index(l, p)
  ensures Inv(l) && p == 0 ==> i == |Seq(l)|
{
  if Inv(l) && ValidPtr(l, p) then l.g[p] else |l.s|
}
 
function method Get<A>(l:DList<A>, p:int):(a:A)
  requires Inv(l)
  requires ValidPtr(l, p)
  ensures a == Seq(l)[Index(l, p)]
{
  seq_get(l.nodes, p).data.value
}
 
function method Next<A>(l:DList<A>, p:int):(p':int)
  requires Inv(l)
  requires MaybePtr(l, p)
  ensures MaybePtr(l, p')
  ensures p == 0 && |Seq(l)| > 0 ==> Index(l, p') == 0
  ensures p == 0 && |Seq(l)| == 0 ==> p' == 0
  ensures p != 0 && Add(Index(l, p), 1) < |Seq(l)| ==> Index(l, p') == Add(Index(l, p), 1)
  ensures p != 0 && Add(Index(l, p), 1) == |Seq(l)| ==> p' == 0
{
  seq_get(l.nodes, p).next
}
 
function method Prev<A>(l:DList<A>, p:int):(p':int)
  requires Inv(l)
  requires MaybePtr(l, p)
  ensures MaybePtr(l, p')
  ensures p == 0 && |Seq(l)| > 0 ==> Index(l, p') == Sub(|Seq(l)|, 1)
  ensures p == 0 && |Seq(l)| == 0 ==> p' == 0
  ensures p != 0 && Index(l, p) > 0 ==> Index(l, p') == Sub(Index(l, p), 1)
  ensures p != 0 && Index(l, p) == 0 == |Seq(l)| ==> p' == 0
{
  seq_get(l.nodes, p).prev
}
 
method BuildFreeStack<A>(a:seq<Node<A>>, k:int) returns(b:seq<Node<A>>)
  requires 0 < k <= |a|
  ensures |b| == |a|
  ensures forall i: int {:trigger b[i]} :: 0 <= i < k ==> b[i] == a[i]
  ensures forall i: int {:trigger b[i]} :: k <= i < |a| ==> b[i] == Node(None, Sub(i, 1), 0)
{
  b := a;
  var n := k;
//   shared_seq_length_bound(b);
  while (n < seq_length(b))
    invariant k <= n <= |b|
    invariant |b| == |a|
    invariant forall i: int :: 0 <= i < k ==> b[i] == a[i]
    invariant forall i: int :: k <= i < n ==> b[i] == Node(None, Sub(i, 1), 0)
    decreases Dec(seq_length(b), n)
  {
    b := seq_set(b, n, Node(None, Sub(n, 1), 0));
    Props_dec_one (seq_length(b));
    Props_dec_lower_bound(seq_length(b), n);
    n := n + 1;
  }
}

// initial_len should be the initial capacity plus 1
method Alloc<A>(initial_len:int) returns(l:DList<A>)
  requires initial_len > 0
  ensures Inv(l)
  ensures Seq(l) == []
{
  var nodes := seq_alloc<Node>(initial_len, Node(None, 0, 0));
  nodes := BuildFreeStack(nodes, 1);
  l := DList(nodes, initial_len - 1, [], [], seq(initial_len, p => if p == 0 then sentinel else unused));
}

method Free<A>(l:DList<A>)
{
  var DList(nodes, freeStack, s, f, g) := l;
  var _ := seq_free(nodes);
}

// 2.486 s
method Expand<A>(l:DList<A>) returns(l':DList<A>)
  requires Inv(l)
  ensures Inv(l')
  ensures l'.s == l.s
  ensures forall x: int {:trigger l'.g[x]} {:trigger ValidPtr(l, x)} {:trigger ValidPtr(l', x)} :: ValidPtr(l, x) ==> ValidPtr(l', x) && l'.g[x] == l.g[x]
  ensures l'.freeStack != 0 && l'.nodes[l'.freeStack].data.None?
{
  var DList(nodes, freeStack, s, f, g) := l;
//   shared_seq_length_bound(nodes);
  var len := seq_length(nodes);
//   shared_seq_length_bound(nodes);
//   var len' := if len < 0x7fff_ffff_ffff_ffff then len + len else len + 1;
  var len' := Add(len, len);
  nodes := SeqResize(nodes, len', Node(None, freeStack, 0));
  assume Add(len, 1) <= Add(len, len);
  nodes := BuildFreeStack(nodes, Add(len, 1));
  l' := DList(nodes, Sub(len', 1), s, f, seq(|nodes|,
    i requires 0 <= i < |nodes| => if i < |g| then g[i] else unused));
}

ghost method Remove_SeqInit(g: seq<int>, index: int) returns (g': seq<int>)
  ensures |g'| == |g|
  ensures forall x: int {:trigger g'[x]} {:trigger g[x]} ::
    0 <= x < |g| ==>
      if g[x] == index then g'[x] == unused
      else if index < g[x] then g'[x] == Sub(g[x], 1)
      else g'[x] == g[x]
  {
    g' := SeqInit(|g|, x requires 0 <= x < |g| =>
    if g[x] == index then unused else if g[x] > index then Sub(g[x], 1) else g[x]);
  }

// 14.353 s
method Remove<A>(l:DList<A>, p:int) returns(l':DList<A>)
  requires Inv(l)
  requires ValidPtr(l, p)
  ensures Inv(l')
  ensures Seq(l') == SeqRemove(Seq(l), Index(l, p))
  ensures forall x: int {:trigger Index(l', x)} {:trigger ValidPtr(l, x)} {:trigger ValidPtr(l', x)} :: x != p && ValidPtr(l, x) ==>
    ValidPtr(l', x) && 
    if Index(l, x) < Index(l, p) then Index(l', x) == Index(l, x)
    else Index(l', x) == Sub(Index(l, x), 1)
{
  // assume forall i: int {:trigger Add(i, 1)} :: Sub(Add(i, 1), 1) == i;
  // assume forall i: int {:trigger Sub(i, 1)} :: Add(Sub(i, 1), 1) == i;
  var DList(nodes, freeStack, s, f, g) := l; 
  ghost var index := g[p];
  ghost var s' := SeqRemove(s, index);
  ghost var f' := SeqRemove(f, index);
  ghost var g' := Remove_SeqInit(g, index);
  var node := seq_get(nodes, p);
  var node_prev := seq_get(nodes, node.prev);
  nodes := seq_set(nodes, node.prev, node_prev.(next := node.next));
  var node_next := seq_get(nodes, node.next);
  nodes := seq_set(nodes, node.next, node_next.(prev := node.prev));
  nodes := seq_set(nodes, p, Node(None, freeStack, 0));
  l' := DList(nodes, p, s', f', g');
}

ghost method InsertAfter_SeqInit(g: seq<int>, p': int, index: int, index': int) returns (g': seq<int>)
  ensures |g'| == |g|
  ensures forall x: int {:trigger g'[x]} {:trigger g[x]} ::
    0 <= x < |g| ==>
      if x == p' then g'[x] == index'
      else if index < g[x] then g'[x] == Add(g[x], 1)
      else g'[x] == g[x]
  {
    g' := SeqInit(|g|, x requires 0 <= x < |g| =>
      if x == p' then index' else if index < g[x] then Add(g[x], 1) else g[x]);
  }

// 64.483 s
method InsertAfter<A>(l:DList<A>, p:int, a:A) returns(l':DList<A>, p':int)
  requires Inv(l)
  requires MaybePtr(l, p)
  ensures Inv(l')
  ensures Seq(l') == SeqInsert(Seq(l), Add(Index(l, p), 1), a)
  ensures ValidPtr(l', p') && Index(l', p') == Add(Index(l, p), 1)
  ensures forall x: int {:trigger Index(l', x)} {:trigger ValidPtr(l, x)} {:trigger ValidPtr(l', x)} :: ValidPtr(l, x) ==>
    ValidPtr(l', x) && 
    if Index(l, x) <= Index(l, p) then Index(l', x) == Index(l, x)
    else Index(l', x) == Add(Index(l, x), 1)
{
  l' := l;
  p' := l'.freeStack;
  var freeNode := seq_get(l'.nodes, p');
  if (p' == 0 || freeNode.data.Some?) {
    l' := Expand(l');
    p' := l'.freeStack;
    freeNode := seq_get(l'.nodes, p');
  }
  var DList(nodes, freeStack, s, f, g) := l';
  ghost var index := g[p];
  ghost var index' := Add(index, 1);
  ghost var s' := SeqInsert(s, index', a);
  ghost var f' := SeqInsert(f, index', p');
  ghost var g' := InsertAfter_SeqInit(g, p', index, index');
  var node := seq_get(nodes, p);
  var node' := Node(Some(a), node.next, p);
  nodes := seq_set(nodes, p, node.(next := p'));
  var node_next := seq_get(nodes, node.next);
  nodes := seq_set(nodes, node.next, node_next.(prev := p'));
  nodes := seq_set(nodes, p', node');
  l' := DList(nodes, freeNode.next, s', f', g');
  // assume forall i: int {:trigger Add(i, 1)} :: Sub(Add(i, 1), 1) == i;
  // assume forall i: int {:trigger Sub(i, 1)} :: Add(Sub(i, 1), 1) == i;
}


ghost method InsertBefore_SeqInit(g: seq<int>, p': int, index': int) returns (g': seq<int>)
  ensures |g'| == |g|
  ensures forall x: int {:trigger g'[x]} {:trigger g[x]} ::
    0 <= x < |g| ==>
      if x == p' then g'[x] == index'
      else if index' <= g[x] then g'[x] == Add(g[x], 1)
      else g'[x] == g[x]
  {
    g' := SeqInit(|g|, x requires 0 <= x < |g| =>
    if x == p' then index' else if g[x] >= index' then Add(g[x], 1) else g[x]);
  }

// 431.236 s
method InsertBefore<A>(l:DList<A>, p:int, a:A) returns(l':DList<A>, p':int)
  requires Inv(l)
  requires MaybePtr(l, p)
  ensures Inv(l')
  ensures Seq(l') == SeqInsert(Seq(l), IndexHi(l, p), a)
  ensures ValidPtr(l', p') && Index(l', p') == IndexHi(l, p)
  ensures forall x: int :: ValidPtr(l, x) ==>
    ValidPtr(l', x) && 
    if Index(l, x) < IndexHi(l, p) then Index(l', x) == Index(l, x)
    else Index(l', x) == Add(Index(l, x), 1)
{
  l' := l;
  p' := l'.freeStack;
  var freeNode := seq_get(l'.nodes, p');
  if (p' == 0 || freeNode.data.Some?) {
    l' := Expand(l');
    p' := l'.freeStack;
    freeNode := seq_get(l'.nodes, p');
  }
  var DList(nodes, freeStack, s, f, g) := l';
  ghost var index' := IndexHi(l, p);
  ghost var s' := SeqInsert(s, index', a);
  ghost var f' := SeqInsert(f, index', p');
  ghost var g' := InsertBefore_SeqInit(g, p', index');
  var node := seq_get(nodes, p);
  var node' := Node(Some(a), p, node.prev);
  nodes := seq_set(nodes, p, node.(prev := p'));
  var node_prev := seq_get(nodes, node.prev);
  nodes := seq_set(nodes, node.prev, node_prev.(next := p'));
  nodes := seq_set(nodes, p', node');
  l' := DList(nodes, freeNode.next, s', f', g');
}

method Clone<A>(l:DList<A>) returns(l':DList<A>)
  ensures l' == l
{
  var DList(nodes, freeStack, s, f, g) := l;
  // shared_seq_length_bound(nodes);
  var nodes' := AllocAndCopy(nodes, 0, seq_length(nodes));
  l' := DList(nodes', freeStack, s, f, g);
}

// 81.178 s
method main()
{
  var l := Alloc<int>(3);
  var p;
  l, p := InsertAfter(l, 0, 100);
  l, p := InsertAfter(l, p, 200);
  l, p := InsertAfter(l, p, 300);
  var p3 := p;
  l, p := InsertAfter(l, p, 400);
  l, p := InsertAfter(l, p, 500);
  assert Seq(l) == [100, 200, 300, 400, 500];
  l := Remove(l, p3);
  assert Seq(l) == [100, 200, 400, 500];
  l, p := InsertAfter(l, p, 600);
  l, p := InsertAfter(l, p, 700);
  assert Seq(l) == [100, 200, 400, 500, 600, 700];
  Free(l);
}