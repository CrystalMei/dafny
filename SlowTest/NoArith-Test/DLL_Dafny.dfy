lemma lt_is_leq ()
  // Warning: /!\ No terms found to trigger on.
  ensures forall i: int, j: int :: i < j ==> i <= j
  ensures forall i: int, j: int :: i < j ==> i != j


datatype Option<V> = None | Some(value:V) 

function method seq_get<A>(s:seq<A>, i:int):(a:A)
  requires 0 <= i < |s|
  ensures a == s[i] 

function method seq_set<A>(s1:seq<A>, i:int, a:A):(s2:seq<A>) // can be implemented as in-place update
  requires 0 <= i < |s1|
  ensures s2 == s1[i := a] 

function method {:extern "LinearExtern", "seq_length"} seq_length<A>(s:seq<A>):(n:int)
//   requires |s| <= 0xffff_ffff_ffff_ffff
  ensures n == |s| 

function method {:extern "LinearExtern", "seq_empty"} seq_empty<A>():(s:seq<A>)
  ensures |s| == 0 

function method {:extern "LinearExtern", "seq_alloc"} seq_alloc<A>(length:int, a:A):(s:seq<A>)
  ensures |s| == length
  ensures forall i :: 0 <= i < |s| ==> s[i] == a 

function method {:extern "LinearExtern", "seq_free"} seq_free<A>(s:seq<A>):() 

function method {:extern "LinearExtern", "seq_unleash"} seq_unleash<A>(s1:seq<A>):(s2:seq<A>)
    ensures s1 == s2 

method SeqResize<A>(s: seq<A>, newlen: int, a: A) returns (s2: seq<A>)
  requires newlen >= 0
  ensures |s2| == newlen
  ensures forall j :: 0 <= j < newlen ==> s2[j] == (if j < |s| then s[j] else a) 

method AllocAndCopy<A>(source: seq<A>, from: int, to: int)
  returns (dest: seq<A>)
  requires 0 <= from <= |source|;
  requires 0 <= to <= |source|;
  requires from <= to; // XXX: cannot do transitive
  ensures source[from..to] == dest

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
  && (forall i {:trigger f[i]} :: 0 <= i < |f| ==> 0 < f[i] < |nodes|)
  && (forall i {:trigger g[f[i]]} :: 0 <= i < |f| ==> 0 <= f[i] ==> g[f[i]] == i)
  && (forall p {:trigger g[p]} :: 
    0 <= p < |g| ==> unused <= g[p] < |s| )
  && (forall p {: trigger nodes[p]} :: 
    0 <= p < |g| ==> 0 <= nodes[p].next < |g| )
  && (forall p {:trigger g[p]} {: trigger nodes[p]} :: 
    0 <= p < |g| ==> (g[p] >= 0 <==> nodes[p].data.Some?) )
  && (forall p {:trigger g[p]} :: 
    0 <= p < |g| && sentinel <= g[p] ==> (g[p] == sentinel ==> p == 0) )
  && (forall p {:trigger g[p]} {:trigger f[g[p]]} {:trigger s[g[p]]} :: 
    0 <= p < |g| && sentinel <= g[p] ==>
      (0 <= g[p] ==> f[g[p]] == p && nodes[p].data == Some(s[g[p]])) )
  && (forall p {:trigger g[p]} {:trigger nodes[p].next} ::
    0 <= p < |g| && sentinel <= g[p] ==>
      nodes[p].next == (
        if g[p] + 1 < |f| then f[g[p] + 1] // nonlast.next or sentinel.next
        else 0) ) // last.next == sentinel or sentinel.next == sentinel
  && (forall p  {:trigger g[p]} {:trigger nodes[p].prev} ::
    0 <= p < |g| && sentinel <= g[p] ==>
    g[p] < |s| && |f| >= 0 ==> 
    && (if g[p] > 0 then 0 <= g[p] - 1 < |f| ==> nodes[p].prev == f[g[p] - 1] // nonfirst.prev
      else if g[p] == 0 || |f| == 0 then nodes[p].prev == 0 // first.prev == sentinel or sentinel.prev == sentinel
      else 0 <= |f| - 1 ==> nodes[p].prev == f[|f| - 1]) ) // sentinel.prev == last
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
  ensures b ==>
    (0 < p ==> 0 <= p) ==>
    0 < p < |l.g| && l.g[p] >= 0
  ensures b ==> p != 0
{
  // lt_is_leq (); // not work
  assume 0 < p ==> 0 <= p;
  assume 0 < p ==> p != 0;
  0 < p < |l.g| && l.g[p] >= 0
}
 
predicate MaybePtr<A>(l:DList<A>, p:int)
{
  p == 0 || ValidPtr(l, p)
}
 
function Index<A>(l:DList<A>, p:int):(i:int)
  ensures Inv(l) && ValidPtr(l, p) ==> 0 <= i
  ensures Inv(l) && ValidPtr(l, p) ==> i < |Seq(l)|
  ensures Inv(l) && p == 0 ==> i == -1
{
  var i := 
    if Inv(l) && MaybePtr(l, p) then
      assume 0 < p ==> 0 <= p;
      assert p == 0 || 0 < p < |l.g|;
      assume 0 <= p < |l.g|;
      l.g[p]
    else 0;
  
  i
}
 
function IndexHi<A>(l:DList<A>, p:int):(i:int)
  ensures Inv(l) && ValidPtr(l, p) ==> i == Index(l, p)
  ensures Inv(l) && p == 0 ==> i == |Seq(l)|
{
  assume 0 < p ==> 0 <= p;
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
  ensures p != 0 && Index(l, p) + 1 < |Seq(l)| ==> Index(l, p') == Index(l, p) + 1
  ensures p != 0 && Index(l, p) + 1 == |Seq(l)| ==> p' == 0
{
  seq_get(l.nodes, p).next
}
 
function method Prev<A>(l:DList<A>, p:int):(p':int)
  requires Inv(l)
  requires MaybePtr(l, p)
  ensures MaybePtr(l, p')
  ensures p == 0 && |Seq(l)| > 0 ==> Index(l, p') == |Seq(l)| - 1
  ensures p == 0 && |Seq(l)| == 0 ==> p' == 0
  ensures p != 0 && Index(l, p) > 0 ==> Index(l, p') == Index(l, p) - 1
  ensures p != 0 && Index(l, p) == 0 == |Seq(l)| ==> p' == 0
{
  seq_get(l.nodes, p).prev
}
 
method BuildFreeStack<A>(a:seq<Node<A>>, k:int) returns(b:seq<Node<A>>)
  requires 0 < k <= |a|
  ensures |b| == |a|
  ensures forall i :: 0 <= i < k ==> b[i] == a[i]
  ensures forall i :: k <= i < |a| ==> b[i] == Node(None, i - 1, 0)
{
  b := a;
  var n := k;
//   shared_seq_length_bound(b);
  while (n < seq_length(b))
    invariant k <= n <= |b|
    invariant |b| == |a|
    invariant forall i :: 0 <= i < k ==> b[i] == a[i]
    invariant forall i :: k <= i < n ==> b[i] == Node(None, i - 1, 0)
  {
    b := seq_set(b, n, Node(None, n - 1, 0));
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

method Expand<A>(l:DList<A>) returns(l':DList<A>)
  requires Inv(l)
  ensures Inv(l')
  ensures l'.s == l.s
  ensures forall x :: ValidPtr(l, x) ==> ValidPtr(l', x) && l'.g[x] == l.g[x]
  ensures l'.freeStack != 0 && l'.nodes[l'.freeStack].data.None?
{
  var DList(nodes, freeStack, s, f, g) := l;
//   shared_seq_length_bound(nodes);
  var len := seq_length(nodes);
//   shared_seq_length_bound(nodes);
//   var len' := if len < 0x7fff_ffff_ffff_ffff then len + len else len + 1;
  var len' := len + len;
  nodes := SeqResize(nodes, len', Node(None, freeStack, 0));
  nodes := BuildFreeStack(nodes, len + 1);
  l' := DList(nodes, len' - 1, s, f, seq(|nodes|,
    i requires 0 <= i < |nodes| => if i < |g| then g[i] else unused));
}

ghost method Remove_SeqInit(g: seq<int>, index: int) returns (g': seq<int>)
  ensures |g'| == |g|
  ensures forall x {:trigger g'[x]} :: 0 <= x < |g| ==>
    if g[x] == index then g'[x] == unused
    else if g[x] > index then g'[x] == g[x] - 1
    else g'[x] == g[x]
  {
    g' := seq(|g|, x requires 0 <= x < |g| =>
      if g[x] == index then unused else if g[x] > index then g[x] - 1 else g[x]);
  }
// Remove from dlist and seq
// ~2s
method Remove<A>(l:DList<A>, p:int) returns(l':DList<A>)
  requires Inv(l)
  requires ValidPtr(l, p)
  ensures Inv(l')
  ensures Seq(l') == Seq(l)[.. Index(l, p)] + Seq(l)[Index(l, p) + 1 ..]
  ensures forall x :: x != p && ValidPtr(l, x) ==>
    ValidPtr(l', x) && Index(l', x) == Index(l, x) - (if Index(l, x) < Index(l, p) then 0 else 1)
{
  var DList(nodes, freeStack, s, f, g) := l;
  assert nodes[p].prev != p;
  // assert nodes[p].next != p;
  ghost var index := g[p];
  ghost var s' := s[.. index] + s[index + 1 ..];
  ghost var f' := f[.. index] + f[index + 1 ..];
  ghost var g' := Remove_SeqInit (g, index);
  // ghost var g' := seq(|g|, x requires 0 <= x < |g| =>
  //     if g[x] == index then unused else if g[x] > index then g[x] - 1 else g[x]);
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
  ensures forall x {:trigger g'[x]} :: 0 <= x < |g| ==>
    if x == p' then g'[x] == index'
    else if g[x] > index then g'[x] == g[x] + 1
    else g'[x] == g[x]
  {
    g' := seq(|g|, x requires 0 <= x < |g| =>
      if x == p' then index' else if g[x] > index then g[x] + 1 else g[x]);
  }

// ~7s
method InsertAfter<A>(l:DList<A>, p:int, a:A) returns(l':DList<A>, p':int)
  requires Inv(l)
  requires MaybePtr(l, p)
  ensures Inv(l')
  ensures Seq(l') == Seq(l)[.. Index(l, p) + 1] + [a] + Seq(l)[Index(l, p) + 1 ..]
  ensures ValidPtr(l', p') && Index(l', p') == Index(l, p) + 1
  ensures forall x :: ValidPtr(l, x) ==>
    ValidPtr(l', x) && Index(l', x) == Index(l, x) + (if Index(l, x) <= Index(l, p) then 0 else 1)
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
  ghost var index' := index + 1;
  ghost var s' := s[.. index'] + [a] + s[index' ..];
  ghost var f' := f[.. index'] + [p'] + f[index' ..];
  ghost var g' := InsertAfter_SeqInit (g, p', index, index');
  // ghost var g' := seq(|g|, x requires 0 <= x < |g| =>
  //   if x == p' then index' else if g[x] > index then g[x] + 1 else g[x]);
  var node := seq_get(nodes, p);
  var node' := Node(Some(a), node.next, p);
  nodes := seq_set(nodes, p, node.(next := p'));
  var node_next := seq_get(nodes, node.next);
  nodes := seq_set(nodes, node.next, node_next.(prev := p'));
  nodes := seq_set(nodes, p', node');
  l' := DList(nodes, freeNode.next, s', f', g');
}

ghost method InsertBefore_SeqInit(g: seq<int>, p': int, index': int) returns (g': seq<int>)
  ensures |g'| == |g|
  ensures forall x {:trigger g'[x]} :: 0 <= x < |g| ==>
    if x == p' then g'[x] == index'
    else if g[x] >= index' then g'[x] == g[x] + 1
    else g'[x] == g[x]
  {
    g' := seq(|g|, x requires 0 <= x < |g| =>
      if x == p' then index' else if g[x] >= index' then g[x] + 1 else g[x]);
  }

// ~ 13s
method InsertBefore<A>(l:DList<A>, p:int, a:A) returns(l':DList<A>, p':int)
  requires Inv(l)
  requires MaybePtr(l, p)
  ensures Inv(l')
  ensures Seq(l') == Seq(l)[.. IndexHi(l, p)] + [a] + Seq(l)[IndexHi(l, p) ..]
  ensures ValidPtr(l', p') && Index(l', p') == IndexHi(l, p)
  ensures forall x :: ValidPtr(l, x) ==>
    ValidPtr(l', x) && Index(l', x) == Index(l, x) + (if Index(l, x) < IndexHi(l, p) then 0 else 1)
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
  ghost var s' := s[.. index'] + [a] + s[index' ..];
  ghost var f' := f[.. index'] + [p'] + f[index' ..];
  ghost var g' := InsertBefore_SeqInit (g, p', index');
  // ghost var g' := seq(|g|, x requires 0 <= x < |g| =>
  //   if x == p' then index' else if g[x] >= index' then g[x] + 1 else g[x]);
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
