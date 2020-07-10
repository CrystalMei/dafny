// include "ADT-int.dfy"
include "ADT-seq.dfy"

newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i < 0x1_0000_0000_0000_0000

// import opened ADT`Basic
import opened ADT`Basic
import opened ADT_Seq`Seq_Basic

datatype Option<V> = None | Some(value:V)
datatype Node<A> = Node(data: Option<A>, next: AbInt, prev: AbInt)
/*
A DList<A> is a doubly-linked list that represents a sequence s of type seq<A>.
It supports efficient insertion and removal but not efficient indexing.
A pointer p of type int is a pointer to a node in the list.
The DList is implemented as a mutable sequence of nodes, where nodes[0] is a sentinel.
*/
// integer: position in seq: index
// integer: position in dlist: pointer
datatype DList<A> = DList(
  nodes:AbSeq<Node<A>>, // sequence of nodes held by the list, indexed by pointer p
  freeStack:AbInt, // pointer to singly-linked stack of free nodes
  ghost s:AbSeq<A>, // sequence of data values held by the list, indexed by integer index i
  ghost f:AbSeq<AbInt>, // map index to pointer: f[i] = p (where p > 0)
  ghost g:AbSeq<AbInt>  // map pointer to index: g[p] = i (where g[p] == -2 means p is unused and g[0] == -1 (sentinel))
  )

ghost const unused: AbInt := AbSub(AbSub(I0, I1), I1) // -2
ghost const sentinel: AbInt := AbSub(I0, I1)// -1

// make sure the list-seq mapping is correct.
predicate Invs<A>(nodes:AbSeq<Node<A>>, freeStack:AbInt, s:AbSeq<A>, f:AbSeq<AbInt>, g:AbSeq<AbInt>)
{
  && AbSeqLen(f) == AbSeqLen(s)
  && AbSeqLen(g) == AbSeqLen(nodes)
  && AbLt(I0, AbSeqLen(nodes))
  && AbSeqIndex(I0, g) == sentinel
  && (AbLt(I0, freeStack) || I0 == freeStack) && AbLt(freeStack, AbSeqLen(nodes))
  // 0 <= i < |f| ==> 0 < f[i] < |nodes|
  && (forall i {:trigger AbSeqIndex(i, f)} ::
    (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(f)) ==>
      AbLt(I0, AbSeqIndex(i, f)) && AbLt(AbSeqIndex(i, f), AbSeqLen(nodes)) )
  // 0 <= i < |f| ==> g[f[i]] == i
  && ( forall i {:trigger AbSeqIndex(AbSeqIndex(i, f), g)} ::
    (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(f)) ==>
      AbSeqIndex(AbSeqIndex(i, f), g) == i )
  // 0 <= p < |g| ==> unused <= g[p] < |s|
  && ( forall p {:trigger AbSeqIndex(p, g)} ::
    (AbLt(I0, p) || I0 == p) && AbLt(p, AbSeqLen(g)) ==>
      (AbLt(unused, AbSeqIndex(p, g)) || unused == AbSeqIndex(p, g)) &&
      AbLt(AbSeqIndex(p, g), AbSeqLen(s)) )
  // 0 <= p < |g| ==> 0 <= nodes[p].next < |g|
  && ( forall p {:trigger AbSeqIndex(p, nodes).next} ::
    (AbLt(I0, p) || I0 == p) && AbLt(p, AbSeqLen(g)) ==>
      (AbLt(I0, AbSeqIndex(p, nodes).next) || I0 == AbSeqIndex(p, nodes).next) &&
      AbLt(AbSeqIndex(p, nodes).next, AbSeqLen(g)) )
  // 0 <= p < |g| ==> (g[p] >= 0 <==> nodes[p].data.Some?)
  && ( forall p {:trigger AbSeqIndex(p, g)} {:trigger AbSeqIndex(p, nodes).data} ::
    (AbLt(I0, p) || I0 == p) && AbLt(p, AbSeqLen(g)) ==>
      ( AbLt(I0, AbSeqIndex(p, g)) || I0 == AbSeqIndex(p, g) <==> AbSeqIndex(p, nodes).data.Some?) )
  // 0 <= p < |g| && sentinel <= g[p] ==> (g[p] == sentinel ==> p == 0)
  && (forall p {:trigger AbSeqIndex(p, g)} ::
    (AbLt(I0, p) || I0 == p) && AbLt(p, AbSeqLen(g)) &&
    (AbLt(sentinel, AbSeqIndex(p, g)) || sentinel == AbSeqIndex(p, g)) ==>
      (AbSeqIndex(p, g) == sentinel ==> p == I0) )
  // 0 <= p < |g| && sentinel <= g[p] ==>
  //    (0 <= g[p] ==> f[g[p]] == p && nodes[p].data == Some(s[g[p]]))
  && (forall p {:trigger AbSeqIndex(p, g)} {:trigger AbSeqIndex(AbSeqIndex(p, g), f)} {:trigger AbSeqIndex(AbSeqIndex(p, g), s)} ::
    (AbLt(I0, p) || I0 == p) && AbLt(p, AbSeqLen(g)) &&
    (AbLt(sentinel, AbSeqIndex(p, g)) || sentinel == AbSeqIndex(p, g)) ==>
      ( AbLt(I0, AbSeqIndex(p, g)) || I0 == AbSeqIndex(p, g) ==>
        AbSeqIndex(AbSeqIndex(p, g), f) == p &&
        AbSeqIndex(p, nodes).data == Some(AbSeqIndex(AbSeqIndex(p, g), s))) )
  // 0 <= p < |g| && sentinel <= g[p] ==>
  //    nodes[p].next == (if g[p] + 1 < |f| then f[g[p] + 1] else 0)
  && ( forall p {:trigger AbSeqIndex(p, g)} {:trigger AbSeqIndex(p, nodes).next} ::
    (AbLt(I0, p) || I0 == p) && AbLt(p, AbSeqLen(g)) &&
    (AbLt(sentinel, AbSeqIndex(p, g)) || sentinel == AbSeqIndex(p, g)) ==>
      (if AbLt(AbAdd(AbSeqIndex(p, g), I1), AbSeqLen(f)) then
        // precond: 0 <= g[p] + 1
        AbLt(I0, AbAdd(AbSeqIndex(p, g), I1)) || I0 == AbAdd(AbSeqIndex(p, g), I1) ==>
        // nonlast.next or sentinel.next
        AbSeqIndex(p, nodes).next == AbSeqIndex(AbAdd(AbSeqIndex(p, g), I1), f)
      // last.next == sentinel or sentinel.next == sentinel
      else AbSeqIndex(p, nodes).next == I0 ) )
  // 0 <= p < |g| && sentinel <= g[p] ==>
  //    nodes[p].prev == (if g[p] > 0 then f[g[p] - 1] else if g[p] == 0 || |f| == 0 then 0 else f[|f| - 1])
  && ( forall p {:trigger AbSeqIndex(p, g)} {:trigger AbSeqIndex(p, nodes).prev} ::
    (AbLt(I0, p) || I0 == p) && AbLt(p, AbSeqLen(g)) &&
    (AbLt(sentinel, AbSeqIndex(p, g)) || sentinel == AbSeqIndex(p, g)) ==>
      if AbLt(I0, AbSeqIndex(p, g)) then
        // precond: 0 <= g[p] - 1
        AbLt(I0, AbSub(AbSeqIndex(p, g), I1)) || I0 == AbSub(AbSeqIndex(p, g), I1) ==>
        // precond: g[p] - 1 < |f|
        AbLt(AbSub(AbSeqIndex(p, g), I1), AbSeqLen(f)) ==>
        // nonfirst.prev
        AbSeqIndex(p, nodes).prev == AbSeqIndex(AbSub(AbSeqIndex(p, g), I1), f)
      else if I0 == AbSeqIndex(p, g) || I0 == AbSeqLen(f) then
        // first.prev == sentinel or sentinel.prev == sentinel
        AbSeqIndex(p, nodes).prev == I0 
      else
        // precond: 0 <= |f| - 1
        AbLt(I0, AbSub(AbSeqLen(f), I1)) || I0 == AbSub(AbSeqLen(f), I1) ==>
        // precond: |f| - 1 < |f|
        AbLt(AbSub(AbSeqLen(f), I1), AbSeqLen(f)) ==>
        // sentinel.prev == last
        AbSeqIndex(p, nodes).prev == AbSeqIndex(AbSub(AbSeqLen(f), I1), f) ) 
}

predicate Inv<A>(l:DList<A>) { Invs(l.nodes, l.freeStack, l.s, l.f, l.g) }

function Seq<A>(l:DList<A>): AbSeq<A> { l.s }

function ValidPtr<A>(l:DList<A>, p:AbInt):(b:bool)
  ensures b ==> p != I0
  {
    // 0 < p < |l.g| && l.g[p] >= 0
    Props_lt_is_not_leq ();
    AbLt(I0, p) && AbLt(p, AbSeqLen(l.g)) &&
    (AbLt(I0, AbSeqIndex(p, l.g)) || I0 == AbSeqIndex(p, l.g))
  }
 
predicate MaybePtr<A>(l:DList<A>, p:AbInt)
  { p == I0 || ValidPtr(l, p) }
 
function Index<A>(l:DList<A>, p:AbInt):(i:AbInt)
  ensures Inv(l) && ValidPtr(l, p) ==> (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(Seq(l)))
  ensures Inv(l) && p == I0 ==> i == AbSub(I0, I1)
  {
    if Inv(l) && MaybePtr(l, p) then AbSeqIndex(p, l.g) else I0
  }

// Remove from dlist and seq
// ~1s
method Remove<A>(l:DList<A>, p:AbInt) returns(l':DList<A>)
  requires Inv(l)
  requires ValidPtr(l, p)
  // ensures Inv(l')
  ensures Seq(l') == AbSeqRemoveIdx(Index(l, p), Seq(l))
  // ensures forall x :: x != p && ValidPtr(l, x) ==> ValidPtr(l', x) && ( if AbLt(Index(l, x), Index(l, p)) then Index(l', x) == Index(l, x) else Index(l', x) == AbSub(Index(l, x), I1) )
  {
    var DList(nodes, freeStack, s, f, g) := l;
    ghost var index := AbSeqIndex(p, g); // I0 <= index
    ghost var s' := AbSeqRemoveIdx(index, s); // s[.. index] + s[index + 1 ..];
    ghost var f' := AbSeqRemoveIdx(index, f); // f[.. index] + f[index + 1 ..];
    ghost var g' := AbSeqInit(AbSeqLen(g), // len >= 0
      x requires (AbLt(I0, x) || I0 == x) && AbLt(x, AbSeqLen(g)) =>
      if AbSeqIndex(x, g) == index then unused
      else if AbLt(index, AbSeqIndex(x, g)) then AbSub(AbSeqIndex(x, g), I1)
      else AbSeqIndex(x, g) );

    Seq_Props_length<AbInt> (); // AbSeqLen(g/f) >= 0
    var node := AbSeqIndex(p, nodes);
    /*** precond for AbSeqIndex(node.prev, nodes) */
    Props_pos(I1);
    Props_leq2lt_sub' (); // sentinel < index
    Props_lt2leq_sub' (); // index > 0 ==> 0 <= index - 1
    Props_add_sub_is_orig ();
    Props_lt_add_notneg (); // index - 1 < |f|
    Props_lt_props_pxy(I0, index);
    assert AbLt(I0, node.prev) || I0 == node.prev; // true
    assert AbLt(node.prev, AbSeqLen(nodes)); // true
    /*** precond ends */
    var node_prev := AbSeqIndex(node.prev, nodes);
    var nodes' := AbSeqUpdate(node.prev, node_prev.(next := node.next), nodes);
    // assert AbSeqIndex(node.prev, nodes').next == node.next;
    var node_next := AbSeqIndex(node.next, nodes');
    // assert if node.next != node.prev then AbSeqIndex(node.next, nodes').next == AbSeqIndex(node.next, nodes).next else true;
    var nodes'' := AbSeqUpdate(node.next, node_next.(prev := node.prev), nodes');
    // assert AbSeqIndex(node.prev, nodes'').next == node.next;
    var nodes''' := AbSeqUpdate(p, Node(None, freeStack, I0), nodes'');

    l' := DList(nodes''', p, s', f', g');

    Props_lt_props_py (index); // ? < index ==> index > ? || index == ?
    assert forall x {:trigger AbSeqIndex(x, l'.g)} :: x != p && ValidPtr(l, x) ==> ValidPtr(l', x); // true
    // assume Inv(l'); // need assume Inv(l') to test this assertion
    // assert forall x {:trigger AbSeqIndex(x, l'.g)} :: x != p && ValidPtr(l, x) ==> ( if AbLt(Index(l, x), Index(l, p)) then Index(l', x) == Index(l, x) else Index(l', x) == AbSub(Index(l, x), I1) ); // true

    /* check Inv(l') */
    Props_add_pos_is_lt ();
    // assert AbSeqLen(f') == AbSeqLen(s'); // true
    // assert AbSeqLen(g') == AbSeqLen(nodes); // true
    // assert AbLt(I0, AbSeqLen(nodes)); // true
    // assert AbLt(I0, index) || I0 == index; // true
    // assert AbSeqIndex(I0, g') == sentinel; // true
    // assert (AbLt(I0, p) || I0 == p ) && AbLt(p, AbSeqLen(nodes''')); // true

    // Props_lt_transitive ();
    // Props_lt_addition ();
    /** test for RemoveIdx postcond */
    assert (forall i : AbInt {:trigger AbSeqIndex(i, f')} :: AbLeqLt(i, I0, index) ==> AbSeqIndex(i, f) == AbSeqIndex(i, f'));    
    assert (forall i : AbInt {:trigger AbSeqIndex(AbAdd(i, I1), f)} {:trigger AbSeqIndex(i, f')} :: AbLeqLt(i, index, AbSeqLen(f')) ==> AbSeqIndex(AbAdd(i, I1), f) == AbSeqIndex(i, f'));

    // // 0 <= i < |f| ==> 0 < f[i] < |nodes|
    // assert (forall i {:trigger AbSeqIndex(i, f')} :: (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(f')) ==> AbLtLt(AbSeqIndex(i, f'), I0, AbSeqLen(nodes''')) );

    // // 0 <= i < |f| ==> g[f[i]] == i
    // assert (forall i {:trigger AbSeqIndex(AbSeqIndex(i, f'), g')} :: AbLeqLt(i, I0, AbSeqLen(f')) ==> AbSeqIndex(AbSeqIndex(i, f'), g') == i );

    // // 0 <= p < |g| ==> unused <= g[p] < |s|
    // assert (forall p {:trigger AbSeqIndex(p, g')} :: AbLeqLt(p, I0, AbSeqLen(g')) ==> AbLeqLt(AbSeqIndex(p, g'), unused, AbSeqLen(s')) );
    
    // // 0 <= p < |g| ==> 0 <= nodes[p].next < |g|
    // assert (forall p {:trigger AbSeqIndex(p, nodes''')} :: AbLeqLt(p, I0, AbSeqLen(g')) ==> AbLeqLt(AbSeqIndex(p, nodes''').next, I0, AbSeqLen(g')) );

    // // 0 <= p < |g| && sentinel <= g[p] ==> (g[p] == sentinel ==> p == 0)
    // assert (forall p {:trigger AbSeqIndex(p, g')} :: AbLeqLt(p, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(p, g')) ==> (AbSeqIndex(p, g') == sentinel ==> p == I0) );

    // // 0 <= p < |g| && sentinel <= g[p] ==> (0 <= g[p] ==> f[g[p]] == p && nodes[p].data == Some(s[g[p]]))
    // assert (forall p {:trigger AbSeqIndex(p, g')} {:trigger AbSeqIndex(AbSeqIndex(p, g'), f')} {:trigger AbSeqIndex(AbSeqIndex(p, g'), s')} :: AbLeqLt(p, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(p, g')) ==> (AbLeq(I0, AbSeqIndex(p, g')) ==> AbSeqIndex(AbSeqIndex(p, g'), f') == p && AbSeqIndex(p, nodes''').data == Some(AbSeqIndex(AbSeqIndex(p, g'), s'))) );

    // assert forall i {:trigger AbAdd(i, I1)} :: AbLt(sentinel, i) ==> AbLt(I0, AbAdd(i, I1));

    /** test for Update postcond */
    // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes')} :: AbLeqLt(i, I0, node.prev) ==> AbSeqIndex(i, nodes) == AbSeqIndex(i, nodes'));
    // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes)} :: AbLtLt(i, node.prev, AbSeqLen(nodes')) ==> AbSeqIndex(i, nodes) == AbSeqIndex(i, nodes'));
    // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes'')} :: AbLeqLt(i, I0, node.next) ==> AbSeqIndex(i, nodes') == AbSeqIndex(i, nodes''));
    // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes'')} :: AbLtLt(i, node.next, AbSeqLen(nodes'')) ==> AbSeqIndex(i, nodes') == AbSeqIndex(i, nodes''));
    // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes''')} :: AbLeqLt(i, I0, p) ==> AbSeqIndex(i, nodes'') == AbSeqIndex(i, nodes'''));
    // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes''')} :: AbLtLt(i, p, AbSeqLen(nodes''')) ==> AbSeqIndex(i, nodes'') == AbSeqIndex(i, nodes'''));

    // // 0 <= p < |g| && sentinel <= g[p] ==> nodes[p].next == (if g[p] + 1 < |f| then f[g[p] + 1] else 0)
    // assert (forall i {:trigger AbSeqIndex(i, g')} {:trigger AbSeqIndex(i, nodes''').next} :: AbLeqLt(i, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(i, g')) ==> (if AbLt(AbAdd(AbSeqIndex(i, g'), I1), AbSeqLen(f')) then AbSeqIndex(i, nodes''').next == AbSeqIndex(AbAdd(AbSeqIndex(i, g'), I1), f') else AbSeqIndex(i, nodes''').next == I0 ) ); // 12s
    
    // // 0 <= p < |g| && sentinel <= g[p] ==> nodes[p].prev == (if g[p] > 0 then f[g[p] - 1] else if g[p] == 0 || |f| == 0 then 0 else f[|f| - 1])
    // assert (forall p {:trigger AbSeqIndex(p, g')} {:trigger AbSeqIndex(p, nodes''').prev} :: AbLeqLt(p, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(p, g')) ==> if AbLt(I0, AbSeqIndex(p, g')) then AbLeq(I0, AbSub(AbSeqIndex(p, g'), I1)) ==> AbLt(AbSub(AbSeqIndex(p, g'), I1), AbSeqLen(f')) ==> AbSeqIndex(p, nodes''').prev == AbSeqIndex(AbSub(AbSeqIndex(p, g'), I1), f') else if I0 == AbSeqIndex(p, g') || I0 == AbSeqLen(f') then AbSeqIndex(p, nodes''').prev == I0 else AbLeq(I0, AbSub(AbSeqLen(f'), I1)) ==> AbLt(AbSub(AbSeqLen(f'), I1), AbSeqLen(f')) ==> AbSeqIndex(p, nodes''').prev == AbSeqIndex(AbSub(AbSeqLen(f'), I1), f') );
    // assert Inv(l');
  }

function IndexHi<A>(l:DList<A>, p:AbInt):(i:AbInt)
  ensures Inv(l) && ValidPtr(l, p) ==> i == Index(l, p)
  ensures Inv(l) && p == I0 ==> i == AbSeqLen(Seq(l))
{
  if Inv(l) && ValidPtr(l, p) then AbSeqIndex(p, l.g) else  AbSeqLen(l.s)
}

method BuildFreeStack<X(==)> (a: AbSeq<Node<X>>, k: AbInt) returns (b: AbSeq<Node<X>>)
  requires AbLt(I0, k)
  requires AbLt(k, AbSeqLen(a)) || k == AbSeqLen(a)
  ensures AbSeqLen(b) == AbSeqLen(a)
  ensures forall i :: (AbLt(I0, i) || I0 == i) && AbLt(i, k) ==>
    AbLt(i, AbSeqLen(a)) ==> // precond: lt_transitive
    AbSeqIndex(i, b) == AbSeqIndex(i, a)
  ensures forall i :: (AbLt(k, i) || k == i) && AbLt(i, AbSeqLen(a)) ==>
    AbLt(I0, i) ==> // precond: lt_transitive
    AbSeqIndex(i, b) == Node(None, AbSub(i, I1), I0)
{
  b := a;
  var n := k;
  Props_lt_transitive'_pxy (I0, k); // 0 < k < ?
  Props_lt_transitive'_pyz (k, AbSeqLen(a)); // ? < k < |a|
  Props_lt_props_py(n); // n < n is wrong
  while AbLt(n, AbSeqLen(b))
    invariant AbLt(k, n) || k == n
    invariant AbLt(n, AbSeqLen(b)) || n == AbSeqLen(b)
    invariant AbSeqLen(b) == AbSeqLen(a)
    invariant forall i: AbInt :: (AbLt(I0, i) || I0 == i) && AbLt(i, k) ==>
      AbLt(i, AbSeqLen(a)) ==> // precond: i < k <= |a|
      AbSeqIndex(i, b) == AbSeqIndex(i, a)
    invariant forall i: AbInt :: (AbLt(k, i) || k == i) && AbLt(i, n) ==>
      AbLt(I0, i) || I0 == i ==> // precond: 0 < k <= i
      AbLt(i, AbSeqLen(a)) ==> // precond: i < n < |a|
      AbSeqIndex(i, b) == Node(None, AbSub(i, I1), I0)
    decreases A2D(AbSub(AbSeqLen(b), n))
  {
    Props_lt_transitive'_pyz (n, AbSeqLen(a)); // ? < n < |a|
    Props_lt_transitive'_p3 (I0, k, n); // n > 0
    Props_lt_transitive'_pxy (I0, n); // 0 < n < ?
    var b' := AbSeqUpdate(n, Node(None, AbSub(n, I1), I0), b); // |b'| == |b|
    // To eval Update
    // assert (forall i {:trigger AbSeqIndex(i, b')} :: (AbLt(I0, i) || I0 == i) && AbLt(i, n) ==> AbSeqIndex(i, b) == AbSeqIndex(i, b'));
    // assert (forall i {:trigger AbSeqIndex(i, b')} :: AbLt(n, i) && AbLt(i, AbSeqLen(b)) ==> AbSeqIndex(i, b) == AbSeqIndex(i, b'));   

    var n' := AbAdd(n, I1);
    Props_pos(I1); // 1 > 0
    Props_add_pos_is_lt (); // x < x + 1
    Props_lt_transitive'_p3 (k, n, n');
    // assert AbLt(k, n'); // k <= n
    Props_lt2leq_add' ();
    // assert AbLt(n', AbSeqLen(b')) || n' == AbSeqLen(b'); // n' <= b

    Props_lt_transitive'_pyz (k, n); // ? < k <= n
    // forall i :: 0 <= i < k ==> b[i] == a[i]
    // assert forall i :: (AbLt(I0, i) || I0 == i) && AbLt(i, k) ==> AbSeqIndex(i, b') == AbSeqIndex(i, a);

    Props_lt_transitive'_pyz (n', AbSeqLen(b'));
    Props_add_sub_is_orig ();
    Props_lt2leq_sub' (); // i < n' ==> i < n || i == n
    // forall i :: k <= i < n ==> b[i] == Node(None, i - 1, 0)
    assert forall i: AbInt :: (AbLt(k, i) || k == i) && AbLt(i, n') ==> AbSeqIndex(i, b') == Node(None, AbSub(i, I1), I0);

    // decreases
    Props_sub_add_is_sub(); // x - (y + 1) == x - y - 1
    // Props_add_sub_is_orig (); // (x - 1) + 1 == x
    Props_adt_dt_lt (AbSub(AbSeqLen(b'), AbAdd(n, I1)), AbSub(AbSeqLen(b'), n));

    n := n';
    b := b';
  }
}

method Expand<X> (l:DList<X>) returns (l':DList<X>)
  requires Inv(l)
  ensures Inv(l')
  ensures l'.s == l.s
  ensures forall x {:trigger AbSeqIndex(x, l'.g)} :: ValidPtr(l, x) ==> ValidPtr(l', x) && AbSeqIndex(x, l'.g) == AbSeqIndex(x, l.g)
  ensures l'.freeStack != I0 && AbSeqIndex(l'.freeStack, l'.nodes).data.None?
{
  var DList(nodes, freeStack, s, f, g) := l;
  var len := AbSeqLen(nodes); // len > 0
  var len' := AbAdd(len, len);
  Props_pos(I1);
  Props_add_pos_is_lt(); // ? < ? + 1, len < len'
  Props_lt_transitive ();
//   Props_lt_transitive'_p3(I0, len, len');  
  var nodes' := AbSeqResize(nodes, len', Node(None, freeStack, I0));

  Props_add_identity (); // 1 <= len
  assert I1 == AbAdd(I0, I1); // trigger
  Props_lt2leq_add' ();
  Props_lt_addition (); // len + 1 <= len + len = len'
  Props_add_commutative ();
//   Props_lt_transitive'_p3(I0, len, AbAdd(len, I1));
  nodes' := BuildFreeStack(nodes', AbAdd(len, I1));

  Seq_Props_length<Node<X>> ();
  // Seq_Props_length<X> ();
  ghost var g' := AbSeqInit( AbSeqLen(nodes'),
    i requires (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(nodes')) =>
      if AbLt(i, AbSeqLen(g)) then AbSeqIndex(i, g) else unused );
  l' := DList(nodes', AbSub(len', I1), s, f, g');

//   Props_lt_transitive'_pyz (len, len');
  // assert forall x : AbInt {:trigger AbSeqIndex(x, l'.g)} :: ValidPtr(l, x) ==> ValidPtr(l', x); // true
  // assert forall x : AbInt {:trigger AbSeqIndex(x, l'.g)} :: ValidPtr(l, x) ==> AbSeqIndex(x, l'.g) == AbSeqIndex(x, l.g); // true

  Props_add_sub_is_orig (); // ? + 1 - 1 == ?
  assert len == AbSub(AbAdd(len, I1), I1); // trigger
  Props_lt_subtraction ();
//   Props_lt_transitive'_p3 (I0, len, AbSub(len', I1)); // 0 < len < len'-1
//   Props_lt_props_pxy (I0, AbSub(len', I1));
//   // assert l'.freeStack != I0; // true
//   // assert AbSeqIndex(l'.freeStack, l'.nodes).data.None?; // true

//   Props_lt_props_px(AbSeqLen(g)); // ? < |g| <==> ? > |g| or ? == |g|
//   Props_lt_transitive'_p3 (unused, sentinel, I0);
//   assert AbLt(unused, I0);
//   Props_lt_transitive'_p3 (unused, I0, AbSeqLen(s)); // unused < |s|

//   // assert forall i :: AbLt(AbSub(i, I1), i);
//   Props_lt_transitive'_pxy(I0, len);
//   Props_lt_transitive'_pyz(AbSub(len', I1), len');
//   assert forall i :: (AbLt(AbAdd(len, I1), i) || AbAdd(len, I1) == i) && AbLt(i, len') ==>
//     (AbLt(len, AbSub(i, I1))|| len == AbSub(i, I1)) && AbLt(AbSub(i, I1), AbSub(len', I1));
//   assert (AbLt(I0, freeStack) || I0 == freeStack) && AbLt(freeStack, len');
//   Props_lt_transitive'_px(I0);
//   Props_lt_transitive'_pz(len');
// //   Props_lt_transitive ();

//   assert forall p {:trigger AbSeqIndex(p, nodes').next} ::
//     (AbLt(I0, p) || I0 == p) && AbLt(p, len') ==>
//       (AbLt(I0, AbSeqIndex(p, nodes').next) || I0 == AbSeqIndex(p, nodes').next) &&
//       AbLt(AbSeqIndex(p, nodes').next, len');

  Props_lt_props ();
  
}

// ~8s
// method InsertAfter<X>(l:DList<X>, p:AbInt, a:X) returns(l':DList<X>, p':AbInt)
//   requires Inv(l)
//   requires MaybePtr(l, p)
//   ensures Inv(l')
//   // ensures Seq(l') == Seq(l)[.. Index(l, p) + 1] + [a] + Seq(l)[Index(l, p) + 1 ..]
//   ensures Seq(l') == AbSeqInsertIdx(AbAdd(Index(l, p), I1), a, Seq(l))
//   ensures ValidPtr(l', p') && Index(l', p') == Index(l, p) + 1
//   ensures forall x :: ValidPtr(l, x) ==>
//     ValidPtr(l', x) && Index(l', x) == Index(l, x) + (if Index(l, x) <= Index(l, p) then 0 else 1)
// {
//   l' := l;
//   p' := l'.freeStack;
//   var freeNode := AbSeqIndex(p', l'.nodes);
//   if (p' == I0 || freeNode.data.Some?) {
//     l' := Expand(l');
//     p' := l'.freeStack;
//     freeNode := AbSeqIndex(p', l'.nodes);
//   }
//   var DList(nodes, freeStack, s, f, g) := l';
//   ghost var index := AbSeqIndex(p, g);
//   ghost var index' := AbAdd(index, I1);
//   ghost var s' := AbSeqInsertIdx(index', a, s);
//   ghost var f' := AbSeqInsertIdx(index', p', f);
//   ghost var g' := AbSeqInit(AbSeqLen(g), x requires AbLeqLt(x, I0, AbSeqLen(g)) =>
//     if x == p' then index'
//     else if AbLt(index, AbSeqIndex(x, g)) then AbAdd(AbSeqIndex(x, g), I1)
//     else AbSeqIndex(x, g));
//   var node := seq_get(nodes, p);
//   var node' := Node(Some(a), node.next, p);
//   nodes := seq_set(nodes, p, node.(next := p'));
//   var node_next := seq_get(nodes, node.next);
//   nodes := seq_set(nodes, node.next, node_next.(prev := p'));
//   nodes := seq_set(nodes, p', node');
//   l' := DList(nodes, freeNode.next, s', f', g');
// }
 
// // ~ 13s
// method InsertBefore<A>(l:DList<A>, p:AbInt, a:A) returns(l':DList<A>, p':AbInt)
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
