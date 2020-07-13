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

// make sure the   list-seq mapping is correct.
predicate Invs<A>(nodes:AbSeq<Node<A>>, freeStack:AbInt, s:AbSeq<A>, f:AbSeq<AbInt>, g:AbSeq<AbInt>)
{
  && AbSeqLen(f) == AbSeqLen(s)
  && AbSeqLen(g) == AbSeqLen(nodes)
  && AbLt(I0, AbSeqLen(nodes))
  && AbSeqIndex(I0, g) == sentinel
  && AbLeqLt(freeStack, I0, AbSeqLen(nodes))
  /* 0 <= i < |f| ==> 0 < f[i] < |nodes| */
  && (forall i {:trigger AbSeqIndex(i, f)} ::
    AbLeqLt(i, I0, AbSeqLen(f)) ==> AbLt(I0, AbSeqIndex(i, f)) && AbLt(AbSeqIndex(i, f), AbSeqLen(nodes)) )
  /* 0 <= i < |f| ==> g[f[i]] == i */
  && (forall i {:trigger AbSeqIndex(AbSeqIndex(i, f), g)} ::
    AbLeqLt(i, I0, AbSeqLen(f)) ==> AbSeqIndex(AbSeqIndex(i, f), g) == i )
  /* 0 <= p < |g| ==> unused <= g[p] < |s| */
  && (forall p {:trigger AbSeqIndex(p, g)} ::
    AbLeqLt(p, I0, AbSeqLen(g)) ==> AbLeqLt(AbSeqIndex(p, g), unused, AbSeqLen(s)) )
  /* 0 <= p < |g| ==> 0 <= nodes[p].next < |g| */
  && (forall p {:trigger AbSeqIndex(p, nodes).next} ::
    AbLeqLt(p, I0, AbSeqLen(g)) ==> AbLeqLt(AbSeqIndex(p, nodes).next, I0, AbSeqLen(g)) )
  /* 0 <= p < |g| ==> (g[p] >= 0 <==> nodes[p].data.Some?) */
  && (forall p /* {:trigger AbSeqIndex(p, g)} */ {:trigger AbSeqIndex(p, nodes).data} ::
    AbLeqLt(p, I0, AbSeqLen(g)) ==> (AbLeq(I0, AbSeqIndex(p, g)) <==> AbSeqIndex(p, nodes).data.Some?) )
  /* 0 <= p < |g| && sentinel <= g[p] ==> (g[p] == sentinel ==> p == 0) */
  && (forall p {:trigger AbSeqIndex(p, g)} ::
    AbLeqLt(p, I0, AbSeqLen(g)) && AbLeq(sentinel, AbSeqIndex(p, g)) ==> (AbSeqIndex(p, g) == sentinel ==> p == I0) )
  /* 0 <= p < |g| && sentinel <= g[p] ==> (0 <= g[p] ==> f[g[p]] == p && nodes[p].data == Some(s[g[p]])) */
  && (forall p /* {:trigger AbSeqIndex(p, g)} */ {:trigger AbSeqIndex(AbSeqIndex(p, g), f)} {:trigger AbSeqIndex(AbSeqIndex(p, g), s)} ::
    AbLeqLt(p, I0, AbSeqLen(g)) && AbLeq(sentinel, AbSeqIndex(p, g)) ==>
      (AbLeq(I0, AbSeqIndex(p, g)) ==>
        AbSeqIndex(AbSeqIndex(p, g), f) == p &&
        AbSeqIndex(p, nodes).data == Some(AbSeqIndex(AbSeqIndex(p, g), s))) )
  /* 0 <= p < |g| && sentinel <= g[p] ==> nodes[p].next == (if g[p] + 1 < |f| then f[g[p] + 1] else 0) */
  && (forall p /* {:trigger AbSeqIndex(p, g)} */ {:trigger AbSeqIndex(p, nodes).next} ::
    AbLeqLt(p, I0, AbSeqLen(g)) && AbLeq(sentinel, AbSeqIndex(p, g)) ==>
      (if AbLt(AbAdd(AbSeqIndex(p, g), I1), AbSeqLen(f)) then
        // precond: 0 <= g[p] + 1
        AbLeq(I0, AbAdd(AbSeqIndex(p, g), I1)) ==>
        // nonlast.next or sentinel.next
        AbSeqIndex(p, nodes).next == AbSeqIndex(AbAdd(AbSeqIndex(p, g), I1), f)
      // last.next == sentinel or sentinel.next == sentinel
      else AbSeqIndex(p, nodes).next == I0 ) )
  /* 0 <= p < |g| && sentinel <= g[p] ==> nodes[p].prev == (if g[p] > 0 then f[g[p] - 1] else if g[p] == 0 || |f| == 0 then 0 else f[|f| - 1]) */
  && (forall p /* {:trigger AbSeqIndex(p, g)} */ {:trigger AbSeqIndex(p, nodes).prev} ::
    AbLeqLt(p, I0, AbSeqLen(g)) && AbLeq(sentinel, AbSeqIndex(p, g)) ==>
      if AbLt(I0, AbSeqIndex(p, g)) then
        // precond: 0 <= g[p] - 1
        AbLeq(I0, AbSub(AbSeqIndex(p, g), I1)) ==>
        // precond: g[p] - 1 < |f|
        AbLt(AbSub(AbSeqIndex(p, g), I1), AbSeqLen(f)) ==>
        // nonfirst.prev
        AbSeqIndex(p, nodes).prev == AbSeqIndex(AbSub(AbSeqIndex(p, g), I1), f)
      else if I0 == AbSeqIndex(p, g) || I0 == AbSeqLen(f) then
        // first.prev == sentinel or sentinel.prev == sentinel
        AbSeqIndex(p, nodes).prev == I0
      else
        // precond: 0 <= |f| - 1
        AbLeq(I0, AbSub(AbSeqLen(f), I1)) ==>
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
    AbLt(I0, p) &&
    AbLt(p, AbSeqLen(l.g)) &&
    AbLeq(I0, AbSeqIndex(p, l.g))
  }
 
predicate MaybePtr<A>(l:DList<A>, p:AbInt)
  { p == I0 || ValidPtr(l, p) }
 
function Index<A>(l:DList<A>, p:AbInt):(i:AbInt)
  ensures Inv(l) && ValidPtr(l, p) ==> AbLeqLt(i, I0, AbSeqLen(Seq(l)))
  ensures Inv(l) && p == I0 ==> i == AbSub(I0, I1)
  {
    if Inv(l) && MaybePtr(l, p) then AbSeqIndex(p, l.g) else I0
  }

// Remove from dlist and seq
// ~1s
method Remove<A>(l:DList<A>, p:AbInt) returns(l':DList<A>)
  requires Inv(l)
  requires ValidPtr(l, p)
  ensures Inv(l')
  ensures Seq(l') == AbSeqRemoveIdx(Index(l, p), Seq(l))
  ensures forall x :: x != p && ValidPtr(l, x) ==> ValidPtr(l', x) && ( if AbLt(Index(l, x), Index(l, p)) then Index(l', x) == Index(l, x) else Index(l', x) == AbSub(Index(l, x), I1) )
  {
    var DList(nodes, freeStack, s, f, g) := l;
    ghost var index := AbSeqIndex(p, g); // index >= 0
    ghost var s' := AbSeqRemoveIdx(index, s); // s[.. index] + s[index + 1 ..];
    ghost var f' := AbSeqRemoveIdx(index, f); // f[.. index] + f[index + 1 ..];
    Seq_Props_length<AbInt> (); // |g| >= 0
    ghost var g' := AbSeqInit(AbSeqLen(g),
      x requires AbLeqLt(x, I0, AbSeqLen(g)) =>
      if AbSeqIndex(x, g) == index then unused
      else if AbLt(index, AbSeqIndex(x, g)) then AbSub(AbSeqIndex(x, g), I1)
      else AbSeqIndex(x, g) );
    var node := AbSeqIndex(p, nodes);

    /*** precond for AbSeqIndex(node.prev, nodes) */
    Props_leq2lt_sub_p2 (I0, index);  // index > sentinel
    Props_lt2leq_sub (); // index > 0 ==> index-1 >= 0, index < |f| ==> index <= |f|-1
    Props_pos(I1);
    Props_add_sub_is_orig (); // Props_add_sub_is_orig_p2 (index, I1);
    // assert index == AbAdd(AbSub(index, I1), I1);
    Props_add_pos_is_lt (); // index-1 < index; index < index+1
    Props_lt_transitive'_p3 (AbSub(index, I1), index, AbSeqLen(f)); // index-1 < index < |f|
    // assert AbLeq(I0, node.prev); // node.prev >= 0
    // assert AbLt(node.prev, AbSeqLen(nodes)); // node.prev < |nodes|
    /*** precond ends */
    var node_prev := AbSeqIndex(node.prev, nodes);
    var nodes' := AbSeqUpdate(node.prev, node_prev.(next := node.next), nodes);
    var node_next := AbSeqIndex(node.next, nodes');
    var nodes'' := AbSeqUpdate(node.next, node_next.(prev := node.prev), nodes');
    var nodes''' := AbSeqUpdate(p, Node(None, freeStack, I0), nodes'');
    l' := DList(nodes''', p, s', f', g');
    
    /** forall x :: x != p && ValidPtr(l, x) ==> ValidPtr(l', x) */
    // Props_lt_transitive'_pxy (I0, index); // 0 < index < x
    
    /** forall x :: x != p && ValidPtr(l, x) ==> Index(l', x) == Index(l, x) - (if Index(l, x) < Index(l, p) then 0 else 1) */
    Props_lt_is_not_leq_px (index);

    /* check Inv(l') */
    /** precond for RemoveIdx */
    assert AbLeq(index, AbSeqLen(f')); // trigger
    Props_lt_transitive'_pyz (index, AbSeqLen(f)); // ? < index < |f|
    Props_lt_transitive'_pyz (index, AbSeqLen(f')); // ? < index <= |f'| = |f|-1
    // assert (forall i : AbInt {:trigger AbSeqIndex(i, f')} :: AbLeqLt(i, I0, index) ==> AbSeqIndex(i, f) == AbSeqIndex(i, f'));
    Props_lt_transitive'_px (I0); // 0 <= index < ? < ? + 1
    // Props_lt_transitive'_px_add (I0); // 0 <= index < ? < ? + 1
    Props_lt_addition_pya (AbSeqLen(f'), I1); // Props_lt_addition ();
    // assert (forall i : AbInt {:trigger AbSeqIndex(AbAdd(i, I1), f)} {:trigger AbSeqIndex(i, f')} :: AbLeqLt(i, index, AbSeqLen(f')) ==> AbSeqIndex(AbAdd(i, I1), f) == AbSeqIndex(i, f'));

    /* 0 <= i < |f| ==> 0 < f[i] < |nodes| */
    // assert (forall i {:trigger AbSeqIndex(i, f')} :: AbLeqLt(i, I0, AbSeqLen(f')) ==> AbLt(I0, AbSeqIndex(i, f')) && AbLt(AbSeqIndex(i, f'), AbSeqLen(nodes''')) );

    /* 0 <= i < |f| ==> g[f[i]] == i */
    Props_lt_transitive'_px(index);
    // assert (forall i {:trigger AbSeqIndex(AbSeqIndex(i, f'), g')} :: AbLeqLt(i, I0, AbSeqLen(f')) ==> AbSeqIndex(AbSeqIndex(i, f'), g') == i );
  
    /* 0 <= p < |g| ==> unused <= g[p] < |s| */
    Props_lt_transitive'_p3 (unused, sentinel, I0); // unused < sentinel < I0
    Props_lt_transitive'_p3 (unused, I0, AbSeqLen(s')); // unused < |s'|
    Props_lt_transitive'_pz_add (AbSeqLen(s'));
    Props_lt_subtraction_pya (AbSeqLen(s), I1);
    // assert (forall p {:trigger AbSeqIndex(p, g')} :: AbLeqLt(p, I0, AbSeqLen(g')) ==> AbLeqLt(AbSeqIndex(p, g'), unused, AbSeqLen(s')) );

    /** precond for Update */
    Props_lt_transitive'_pz (AbSeqLen(nodes));
    // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes')} :: AbLeqLt(i, I0, node.prev) ==> AbSeqIndex(i, nodes) == AbSeqIndex(i, nodes'));
    // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes)} :: AbLtLt(i, node.prev, AbSeqLen(nodes')) ==> AbSeqIndex(i, nodes) == AbSeqIndex(i, nodes'));
    // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes'')} :: AbLeqLt(i, I0, node.next) ==> AbSeqIndex(i, nodes') == AbSeqIndex(i, nodes''));
    // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes'')} :: AbLtLt(i, node.next, AbSeqLen(nodes'')) ==> AbSeqIndex(i, nodes') == AbSeqIndex(i, nodes''));
    // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes''')} :: AbLeqLt(i, I0, p) ==> AbSeqIndex(i, nodes'') == AbSeqIndex(i, nodes'''));
    // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes''')} :: AbLtLt(i, p, AbSeqLen(nodes''')) ==> AbSeqIndex(i, nodes'') == AbSeqIndex(i, nodes'''));

    /* 0 <= p < |g| ==> 0 <= nodes[p].next < |g| */
    Props_lt_is_not_leq_px (node.prev);
    Props_lt_is_not_leq_px (node.next);
    Props_lt_is_not_leq_px (p);
    // assert (forall p {:trigger AbSeqIndex(p, nodes''').next} :: AbLeqLt(p, I0, AbSeqLen(g')) ==> AbLeqLt(AbSeqIndex(p, nodes''').next, I0, AbSeqLen(g')) );

    /* 0 <= p < |g| ==> (g[p] >= 0 <==> nodes[p].data.Some?) */
    Props_lt_is_not_leq_px (I0);
    // assert (forall p {:trigger AbSeqIndex(p, nodes''').data} :: AbLeqLt(p, I0, AbSeqLen(g')) ==> (AbLeq(I0, AbSeqIndex(p, g')) <==> AbSeqIndex(p, nodes''').data.Some?) );
    
    /* 0 <= p < |g| && sentinel <= g[p] ==> (g[p] == sentinel ==> p == 0) */
    // assert (forall p {:trigger AbSeqIndex(p, g')} :: AbLeqLt(p, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(p, g')) ==> (AbSeqIndex(p, g') == sentinel ==> p == I0) );

    /* 0 <= p < |g| && sentinel <= g[p] ==> (0 <= g[p] ==> f[g[p]] == p && nodes[p].data == Some(s[g[p]])) */
    // Props_lt_subtraction ();  
    Props_lt_transitive'_pxy (sentinel, I0);
    // assert (forall p {:trigger AbSeqIndex(AbSeqIndex(p, g'), f')} :: AbLeqLt(p, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(p, g')) ==> (AbLeq(I0, AbSeqIndex(p, g')) ==> AbSeqIndex(AbSeqIndex(p, g'), f') == p));
    // assert (forall p {:trigger AbSeqIndex(AbSeqIndex(p, g'), f')} {:trigger AbSeqIndex(AbSeqIndex(p, g'), s')} :: AbLeqLt(p, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(p, g')) ==> (AbLeq(I0, AbSeqIndex(p, g')) ==> AbSeqIndex(p, nodes''').data == Some(AbSeqIndex(AbSeqIndex(p, g'), s'))) );

    /* 0 <= p < |g| && sentinel <= g[p] ==> nodes[p].next == (if g[p] + 1 < |f| then f[g[p] + 1] else 0) */
    // index + 1 < |f| ==> nodes[p].next == f[index + 1]
    // assert if AbLt(AbAdd(index, I1), AbSeqLen(f)) then AbSeqIndex(p, nodes).next == AbSeqIndex(AbAdd(index, I1), f) else AbSeqIndex(p, nodes).next == I0;
    Props_lt_addition_pxa (sentinel, I1);
    // assert (forall i {:trigger AbSeqIndex(i, nodes''').next} :: AbLeqLt(i, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(i, g')) ==> (if AbLt(AbAdd(AbSeqIndex(i, g'), I1), AbSeqLen(f')) then AbSeqIndex(i, nodes''').next == AbSeqIndex(AbAdd(AbSeqIndex(i, g'), I1), f') else AbSeqIndex(i, nodes''').next == I0 ) );
    
    /* 0 <= p < |g| && sentinel <= g[p] ==> nodes[p].prev == (if g[p] > 0 then f[g[p] - 1] else if g[p] == 0 || |f| == 0 then 0 else f[|f| - 1]) */
    // assert (forall p {:trigger AbSeqIndex(p, nodes''').prev} :: AbLeqLt(p, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(p, g')) ==> if AbLt(I0, AbSeqIndex(p, g')) then AbLeq(I0, AbSub(AbSeqIndex(p, g'), I1)) ==> AbLt(AbSub(AbSeqIndex(p, g'), I1), AbSeqLen(f')) ==> AbSeqIndex(p, nodes''').prev == AbSeqIndex(AbSub(AbSeqIndex(p, g'), I1), f') else if I0 == AbSeqIndex(p, g') || I0 == AbSeqLen(f') then AbSeqIndex(p, nodes''').prev == I0 else AbLeq(I0, AbSub(AbSeqLen(f'), I1)) ==> AbLt(AbSub(AbSeqLen(f'), I1), AbSeqLen(f')) ==> AbSeqIndex(p, nodes''').prev == AbSeqIndex(AbSub(AbSeqLen(f'), I1), f') );
  }

function IndexHi<A>(l:DList<A>, p:AbInt):(i:AbInt)
  ensures Inv(l) && ValidPtr(l, p) ==> i == Index(l, p)
  ensures Inv(l) && p == I0 ==> i == AbSeqLen(Seq(l))
{
  if Inv(l) && ValidPtr(l, p) then AbSeqIndex(p, l.g) else  AbSeqLen(l.s)
}

method BuildFreeStack<X(==)> (a: AbSeq<Node<X>>, k: AbInt) returns (b: AbSeq<Node<X>>)
  requires AbLt(I0, k)
  requires AbLeq(k, AbSeqLen(a))
  ensures AbSeqLen(b) == AbSeqLen(a)
  ensures forall i {:trigger AbSeqIndex(i, b)} :: AbLeqLt(i, I0, k) ==>
    AbLt(i, AbSeqLen(a)) ==> // precond: lt_transitive
    AbSeqIndex(i, b) == AbSeqIndex(i, a)
  ensures forall i {:trigger AbSeqIndex(i, b)} :: AbLeqLt(i, k, AbSeqLen(a)) ==>
    AbLeq(I0, i) ==> // precond: lt_transitive
    AbSeqIndex(i, b) == Node(None, AbSub(i, I1), I0)
{
  b := a;
  var n := k;
  Props_lt_is_not_leq ();
  Props_lt_transitive' ();
  while AbLt(n, AbSeqLen(b))
    invariant AbLeq(k, n)
    invariant AbLeq(n, AbSeqLen(b))
    invariant AbSeqLen(b) == AbSeqLen(a)
    invariant forall i: AbInt :: AbLeqLt(i, I0, k) ==>
      AbLt(i, AbSeqLen(a)) ==> // precond: lt_transitive
      AbSeqIndex(i, b) == AbSeqIndex(i, a)
    invariant forall i: AbInt :: AbLeqLt(i, k, n) ==>
      AbLeq(I0, i) ==> // precond: lt_transitive
      AbLt(i, AbSeqLen(b)) ==> // precond: lt_transitive
      AbSeqIndex(i, b) == Node(None, AbSub(i, I1), I0)
    decreases A2D(AbSub(AbSeqLen(b), n))
  {
    Props_lt_transitive'_pyz (n, AbSeqLen(a)); // ? < n < |a|
    Props_lt_transitive'_p3 (I0, k, n); // n > 0
    Props_lt_transitive'_pxy (I0, n); // 0 < n < ?
    var b' := AbSeqUpdate(n, Node(None, AbSub(n, I1), I0), b);

    var n' := AbAdd(n, I1);
    Props_pos(I1); // 1 > 0
    Props_add_pos_is_lt (); // x < x + 1
    Props_lt_transitive'_p3 (k, n, n'); // k <= n'
    Props_lt2leq_add (); // n' <= b
    Props_lt_transitive'_pyz (k, n); // ? < k <= n
    // forall i :: 0 <= i < k ==> b[i] == a[i]

    Props_lt_transitive'_pyz (n', AbSeqLen(b'));
    Props_add_sub_is_orig ();
    Props_lt2leq_sub (); // i < n' ==> i < n || i == n
    // forall i :: k <= i < n ==> b[i] == Node(None, i - 1, 0)

    // decreases
    Props_sub_add_is_sub(); // x - (y + 1) == x - y - 1
    Props_add_pos_is_lt (); // x < x + 1
    // Props_add_sub_is_orig (); // (x - 1) + 1 == x
    Props_adt_dt_lt (AbSub(AbSeqLen(b'), AbAdd(n, I1)), AbSub(AbSeqLen(b'), n));

    n := AbAdd(n, I1);
    b := b';
  }
}

method Expand<X> (l:DList<X>) returns (l':DList<X>)
  requires Inv(l)
  ensures Inv(l')
  ensures l'.s == l.s
  ensures forall x {:trigger AbSeqIndex(x, l'.g)} {:trigger ValidPtr(l', x)} :: ValidPtr(l, x) ==> 
    ValidPtr(l', x) && AbSeqIndex(x, l'.g) == AbSeqIndex(x, l.g)
  ensures l'.freeStack != I0 && AbSeqIndex(l'.freeStack, l'.nodes).data.None?
{
  var DList(nodes, freeStack, s, f, g) := l;
  var len := AbSeqLen(nodes); // len > 0
  var len' := AbAdd(len, len);
  var nodes' := AbSeqResize(nodes, len', Node(None, freeStack, I0));

  Props_pos(I1);
  Props_add_pos_is_lt(); // len < len+1, len < len'
  Props_lt_transitive'_p3(I0, len, len'); // 0 < len'
  Props_lt2leq_add_p2(I0, len); // Props_lt2leq_add(); // both work
  Props_add_identity (); // 1 <= len
  Props_add_commutative ();
  Props_lt_addition (); // len + 1 <= len + len = len'
  Props_lt_transitive'_p3(I0, len, AbAdd(len, I1));
  nodes' := BuildFreeStack(nodes', AbAdd(len, I1));

  Seq_Props_length<Node<X>> ();
  ghost var g' := AbSeqInit( AbSeqLen(nodes'),
    i requires AbLeqLt(i, I0, AbSeqLen(nodes')) =>
      if AbLt(i, AbSeqLen(g)) then AbSeqIndex(i, g) else unused );
  l' := DList(nodes', AbSub(len', I1), s, f, g');

  Props_lt_transitive'_pyz (len, len');
  Props_add_sub_is_orig ();
  assert len == AbSub(AbAdd(len, I1), I1); // trigger
  Props_lt_subtraction (); // len <= len'-1
  Props_lt_transitive'_p3 (I0, len, AbSub(len', I1)); // 0 < len < len'-1
  Props_lt_is_not_leq_px (AbAdd(len, I1));
  // Props_lt_is_not_leq_py (AbAdd(len, I1));

  /* 0 <= p < |g| ==> unused <= g[p] < |s| */
  Props_lt_transitive'_p3 (unused, sentinel, I0); // unused < sentinel < I0
  Props_lt_transitive'_pz(AbSeqLen(s)); // ? < ? < |s|

  /* 0 <= p < |g| ==> 0 <= nodes[p].next < |g| */
  assert AbLt(I0, AbAdd(len, I1));
  Props_lt_transitive'_pxy (I0, len); // 0 < len < ?
  Props_lt_transitive'_pyz(AbSub(len', I1), len'); // ? < |g'| - 1 < |g'|

  /* 0 <= p < |g| ==> (g[p] >= 0 <==> nodes[p].data.Some?) */
  Props_lt_transitive'_pxy(unused, I0); // g'[p] >= 0 ==> 0 <= p < len
  Props_lt_transitive'_pyz(len, AbAdd(len, I1));
}

method InsertAfter<X>(l:DList<X>, p:AbInt, a:X) returns(l':DList<X>, p':AbInt)
  requires Inv(l)
  requires MaybePtr(l, p)
  // ensures Inv(l')
  ensures AbLeqLt(AbAdd(Index(l, p), I1), I0, AbSeqLen(Seq(l))) ==> // precond
    Seq(l') == AbSeqInsertIdx(AbAdd(Index(l, p), I1), a, Seq(l))
  // ensures ValidPtr(l', p') && Index(l', p') == AbAdd(Index(l, p), I1)
  // ensures forall x :: ValidPtr(l, x) ==> ValidPtr(l', x) && if AbLeq(Index(l, x), Index(l, p)) then Index(l', x) == Index(l, x) else Index(l', x) == AbAdd(Index(l, x), I1)
{
  var l_exp := l;
  p' := l_exp.freeStack;
  var freeNode := AbSeqIndex(p', l_exp.nodes);
  if (p' == I0 || freeNode.data.Some?) {
    l_exp := Expand(l_exp);
    p' := l_exp.freeStack;
    freeNode := AbSeqIndex(p', l_exp.nodes);
  }
  var DList(nodes, freeStack, s, f, g) := l_exp;
  assert ValidPtr(l, p) ==> ValidPtr(l_exp, p); // trigger
  ghost var index := AbSeqIndex(p, g); //  p == 0 || (0 < p < |g| && index >= 0)
  ghost var index' := AbAdd(index, I1);
  /** precond for AbSeqInsertIdx */
  Props_pos(I1);
  Props_add_sub_is_orig ();
  assert I0 == AbAdd(AbSub(I0, I1), I1); // trigger
  Props_lt_addition ();
  Props_add_pos_is_lt ();
  Props_lt_transitive'_p3 (I0, index, index'); // index' >= 0
  Props_lt2leq_add (); // index' < |s| + 1 ==> index' <= |s|
  /** precond ends */
  ghost var s' := AbSeqInsertIdx(index', a, s);
  ghost var f' := AbSeqInsertIdx(index', p', f);
  ghost var g' := AbSeqInit(AbSeqLen(g), x requires AbLeqLt(x, I0, AbSeqLen(g)) =>
    if x == p' then index'
    else if AbLt(index, AbSeqIndex(x, g)) then AbAdd(AbSeqIndex(x, g), I1)
    else AbSeqIndex(x, g));
  var node := AbSeqIndex(p, nodes);
  var node' := Node(Some(a), node.next, p);
  nodes := AbSeqUpdate(p, node.(next := p'), nodes);
  var node_next := AbSeqIndex(node.next, nodes);
  nodes := AbSeqUpdate(node.next, node_next.(prev := p'), nodes);
  nodes := AbSeqUpdate(p', node', nodes);
  l' := DList(nodes, freeNode.next, s', f', g');

  /** ValidPtr(l', p') && Index(l', p') == Index(l, p) + 1 */

  /** forall x :: ValidPtr(l, x) ==> ValidPtr(l', x) && Index(l', x) == Index(l, x) + (if Index(l, x) <= Index(l, p) then 0 else 1) */
  Props_lt_is_not_leq_px (index);
  Props_lt_transitive'_px_add(I0);
  assert forall x {:trigger ValidPtr(l, x)} :: ValidPtr(l, x) ==> ValidPtr(l_exp, x); // trigger

  /* check Inv(l') */
  /** g[0] == sentinel */
  Props_lt_is_not_leq_px (I0); // sentinel < (!=) 0
  
  /** postcond for InsertIdx */
  Props_lt_transitive'_pyz(index', AbSeqLen(s));
  Props_lt_transitive'_pyz(index', AbSeqLen(s'));
  Props_lt_transitive'_pxy(I0, index'); // 0 <= index' < ?
  Props_lt_transitive'_pxy(sentinel, index); // sentinel <= index < ?
  Props_lt_transitive'_pyz(AbSeqLen(s), AbSeqLen(s'));
  // assert forall i {:trigger AbSeqIndex(i, s')} :: AbLeqLt(i, I0, index') ==> AbSeqIndex(i, s') == AbSeqIndex(i, s);
  assert forall i {:trigger AbSeqIndex(AbSub(i, I1), s)} :: AbLt(index', i) && AbLt(i, AbSeqLen(s')) ==> AbSeqIndex(AbSub(i, I1), s) == AbSeqIndex(i, s');

  /* 0 <= i < |f| ==> 0 < f[i] < |nodes| */
  Props_lt_is_not_leq_px (index');
  assert (forall i {:trigger AbSeqIndex(i, f)} :: AbLeqLt(i, I0, AbSeqLen(f)) ==> AbLt(I0, AbSeqIndex(i, f)) && AbLt(AbSeqIndex(i, f), AbSeqLen(nodes)) );
  assert forall i :: AbLeqLt(i, I0, AbSeqLen(f)) ==> AbLeqLt(i, I0, AbSeqLen(f'));
  assert AbLt(I0, p'); assert AbLt(p', AbSeqLen(nodes));
  assert (forall i {:trigger AbSeqIndex(i, f')} :: AbLeqLt(i, I0, AbSeqLen(f')) ==> AbLt(I0, AbSeqIndex(i, f')) && AbLt(AbSeqIndex(i, f'), AbSeqLen(nodes)) );

}
 
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
