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
  && AbLt(I0, AbSeqLen(nodes)) /* |nodes| > 0 */
  && AbSeqIndex(I0, g) == sentinel /* g[0] == sentinel */
  /* 0 <= freeStack < |nodes| */
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
  /* 0 <= p < |g| && sentinel <= g[p] ==> (0 <= g[p] ==> f[g[p]] == p) */
  && (forall p /* {:trigger AbSeqIndex(p, g)} */ {:trigger AbSeqIndex(AbSeqIndex(p, g), f)} ::
    AbLeqLt(p, I0, AbSeqLen(g)) && AbLeq(sentinel, AbSeqIndex(p, g)) ==>
      (AbLeq(I0, AbSeqIndex(p, g)) ==>
        AbSeqIndex(AbSeqIndex(p, g), f) == p) )
  /* 0 <= p < |g| && sentinel <= g[p] ==> (0 <= g[p] ==> nodes[p].data == Some(s[g[p]])) */
  && (forall p /* {:trigger AbSeqIndex(p, g)} */ {:trigger AbSeqIndex(AbSeqIndex(p, g), s)} ::
    AbLeqLt(p, I0, AbSeqLen(g)) && AbLeq(sentinel, AbSeqIndex(p, g)) ==>
      (AbLeq(I0, AbSeqIndex(p, g)) ==>
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

ghost method Remove_SeqInit(g: AbSeq<AbInt>, index: AbInt) returns (g': AbSeq<AbInt>)
  ensures AbSeqLen(g') == AbSeqLen(g)
  ensures forall x {:trigger AbSeqIndex(x, g')} {:trigger AbSeqIndex(x, g)} ::
    AbLeqLt(x, I0, AbSeqLen(g)) ==>
      if AbSeqIndex(x, g) == index then AbSeqIndex(x, g') == unused
      else if AbLt(index, AbSeqIndex(x, g)) then AbSeqIndex(x, g') == AbSub(AbSeqIndex(x, g), I1)
      else AbSeqIndex(x, g') == AbSeqIndex(x, g)
  {
    Seq_Props_length<AbInt> ();
    g' := AbSeqInit(AbSeqLen(g),
      x requires AbLeqLt(x, I0, AbSeqLen(g)) =>
      if AbSeqIndex(x, g) == index then unused
      else if AbLt(index, AbSeqIndex(x, g)) then AbSub(AbSeqIndex(x, g), I1)
      else AbSeqIndex(x, g) );
  }

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
    ghost var g' := Remove_SeqInit (g, index);
    var node := AbSeqIndex(p, nodes);

    /*** precond for AbSeqIndex(node.prev, nodes) */
    Props_leq2lt_sub_p2 (I0, index);  // index > sentinel
    Props_lt2leq_sub (); // index > 0 ==> index-1 >= 0, index < |f| ==> index <= |f|-1
    Props_pos(I1);
    Props_add1sub1_is_orig (); // Props_add_sub_is_orig ();
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
    Props_lt_transitive'_pxy (I0, index); // 0 < index < x
    
    /** forall x :: x != p && ValidPtr(l, x) ==> Index(l', x) == Index(l, x) - (if Index(l, x) < Index(l, p) then 0 else 1) */
    Props_lt_is_not_leq_px (index);

    /* check Inv(l') */
    /** precond for RemoveIdx */
    assert AbLeq(index, AbSeqLen(f')); // trigger
    Props_lt_transitive'_pyz (index, AbSeqLen(f)); // ? < index < |f|
    Props_lt_transitive'_pyz (index, AbSeqLen(f')); // ? < index <= |f'| = |f|-1
    // assert (forall i : AbInt {:trigger AbSeqIndex(i, f')} :: AbLeqLt(i, I0, index) ==> AbSeqIndex(i, f) == AbSeqIndex(i, f'));
    // Props_lt_transitive'_px (I0); // 0 <= index < ? < ? + 1
    Props_lt_transitive'_px_add (I0); // 0 <= index < ? < ? + 1
    Props_lt_addition_pya (AbSeqLen(f'), I1); // Props_lt_addition ();
    // assert (forall i : AbInt {:trigger AbSeqIndex(AbAdd(i, I1), f)} {:trigger AbSeqIndex(i, f')} :: AbLeqLt(i, index, AbSeqLen(f')) ==> AbSeqIndex(AbAdd(i, I1), f) == AbSeqIndex(i, f'));

    /* 0 <= i < |f| ==> 0 < f[i] < |nodes| */
    // assert (forall i {:trigger AbSeqIndex(i, f')} :: AbLeqLt(i, I0, AbSeqLen(f')) ==> AbLt(I0, AbSeqIndex(i, f')) && AbLt(AbSeqIndex(i, f'), AbSeqLen(nodes''')) );

    /* 0 <= i < |f| ==> g[f[i]] == i */
    Props_lt_transitive'_px_add(index);
    // assert (forall i {:trigger AbSeqIndex(AbSeqIndex(i, f'), g')} :: AbLeqLt(i, I0, AbSeqLen(f')) ==> AbSeqIndex(AbSeqIndex(i, f'), g') == i );
  
    /* 0 <= p < |g| ==> unused <= g[p] < |s| */
    Props_lt_transitive'_p3 (unused, sentinel, I0); // unused < sentinel < I0
    Props_lt_transitive'_p3 (unused, I0, AbSeqLen(s')); // unused < |s'|
    Props_lt_transitive'_pz_add (AbSeqLen(s'));
    Props_lt_subtraction_pya (AbSeqLen(s), I1);
    // assert (forall p {:trigger AbSeqIndex(p, g')} :: AbLeqLt(p, I0, AbSeqLen(g')) ==> AbLeqLt(AbSeqIndex(p, g'), unused, AbSeqLen(s')) );

    /** precond for Update */
    Props_lt_transitive'_pz_add (AbSeqLen(nodes));
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
    // assert (forall p {:trigger AbSeqIndex(AbSeqIndex(p, g'), s')} :: AbLeqLt(p, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(p, g')) ==> (AbLeq(I0, AbSeqIndex(p, g')) ==> AbSeqIndex(p, nodes''').data == Some(AbSeqIndex(AbSeqIndex(p, g'), s'))) );

    /* 0 <= p < |g| && sentinel <= g[p] ==> nodes[p].next == (if g[p] + 1 < |f| then f[g[p] + 1] else 0) */
    // index + 1 < |f| ==> nodes[p].next == f[index + 1]
    // assert if AbLt(AbAdd(index, I1), AbSeqLen(f)) then AbSeqIndex(p, nodes).next == AbSeqIndex(AbAdd(index, I1), f) else AbSeqIndex(p, nodes).next == I0;
    Props_lt_addition_pxa (sentinel, I1);
    // assert (forall i {:trigger AbSeqIndex(i, nodes''').next} :: AbLeqLt(i, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(i, g')) ==> (if AbLt(AbAdd(AbSeqIndex(i, g'), I1), AbSeqLen(f')) then AbSeqIndex(i, nodes''').next == AbSeqIndex(AbAdd(AbSeqIndex(i, g'), I1), f') else AbSeqIndex(i, nodes''').next == I0 ) );
    
    /* 0 <= p < |g| && sentinel <= g[p] ==> nodes[p].prev == (if g[p] > 0 then f[g[p] - 1] else if g[p] == 0 || |f| == 0 then 0 else f[|f| - 1]) */
    Props_lt_addition_pya (index, I1);
    // assert (forall p {:trigger AbSeqIndex(p, nodes''').prev} :: AbLeqLt(p, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(p, g')) ==> if AbLt(I0, AbSeqIndex(p, g')) then AbLeq(I0, AbSub(AbSeqIndex(p, g'), I1)) ==> AbLt(AbSub(AbSeqIndex(p, g'), I1), AbSeqLen(f')) ==> AbSeqIndex(p, nodes''').prev == AbSeqIndex(AbSub(AbSeqIndex(p, g'), I1), f') else if I0 == AbSeqIndex(p, g') || I0 == AbSeqLen(f') then AbSeqIndex(p, nodes''').prev == I0 else AbLeq(I0, AbSub(AbSeqLen(f'), I1)) ==> AbLt(AbSub(AbSeqLen(f'), I1), AbSeqLen(f')) ==> AbSeqIndex(p, nodes''').prev == AbSeqIndex(AbSub(AbSeqLen(f'), I1), f') );
  }

function IndexHi<A>(l:DList<A>, p:AbInt):(i:AbInt)
  ensures Inv(l) && ValidPtr(l, p) ==> i == Index(l, p)
  ensures Inv(l) && p == I0 ==> i == AbSeqLen(Seq(l))
{
  if Inv(l) && ValidPtr(l, p) then AbSeqIndex(p, l.g) else AbSeqLen(l.s)
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

function method AbSeqAlloc<A>(length:AbInt, a:A): (s:AbSeq<A>)
  ensures AbSeqLen(s) == length
  ensures forall i :: AbLeqLt(i, I0, AbSeqLen(s)) ==> AbSeqIndex(i, s) == a

// initial_len should be the initial capacity plus 1
method Alloc<A>(initial_len: AbInt) returns(l:DList<A>)
  requires AbLt(I0, initial_len)
  ensures Inv(l)
  ensures Seq(l) == AbSeqEmpty<A> ()
{
  var nodes := AbSeqAlloc(initial_len, Node(None, I0, I0));
  Props_pos(I1); Props_add_pos_is_lt ();
  Props_add_identity ();
  Props_lt2leq_add_p2(I0, initial_len); // 0 < initial_len ==> 1 <= initial_len
  nodes := BuildFreeStack(nodes, I1);
  ghost var g := AbSeqInit(initial_len, p => if p == I0 then sentinel else unused);
  l := DList(nodes, AbSub(initial_len, I1), AbSeqEmpty<A> (), AbSeqEmpty<AbInt> (), g);

  /* 0 <= freeStack < |nodes| */
  Props_lt2leq_sub_p2(I0, initial_len); // initial_len - 1 >= 0
  Props_add1sub1_is_orig ();

  /* 0 <= i < |f| ==> 0 < f[i] < |nodes| */
  Props_lt_is_not_leq_px (I0);

  /* 0 <= p < |g| ==> unused <= g[p] < |s| */
  Props_lt_transitive'_p3(unused, sentinel, I0);

  /* 0 <= p < |g| ==> 0 <= nodes[p].next < |g| */
  Props_lt_is_not_leq_px (I1);
  Props_lt_subtraction ();
  Props_add2sub ();
  Props_lt_transitive'_px(I0); // 1 <= i ==> 0 <= i - 1
  Props_lt_transitive'_pz(initial_len);
}

function method AbSeqFree<A>(s:AbSeq<A>):()
method Free<A>(l:DList<A>)
{
  var DList(nodes, freeStack, s, f, g) := l;
  var _ := AbSeqFree(nodes);
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
  Props_pos(I1);
  Props_add_pos_is_lt(); // len < len+1, len < len'
  Props_lt_transitive'_p3(I0, len, len'); // 0 < len'
  var nodes' := AbSeqResize(nodes, len', Node(None, freeStack, I0));

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

ghost method InsertAfter_SeqInit(g: AbSeq<AbInt>, p': AbInt, index: AbInt, index': AbInt) returns (g': AbSeq<AbInt>)
  ensures AbSeqLen(g') == AbSeqLen(g)
  ensures forall x {:trigger AbSeqIndex(x, g')} {:trigger AbSeqIndex(x, g)} ::
    AbLeqLt(x, I0, AbSeqLen(g)) ==>
      if x == p' then AbSeqIndex(x, g') == index'
      else if AbLt(index, AbSeqIndex(x, g)) then AbSeqIndex(x, g') == AbAdd(AbSeqIndex(x, g), I1)
      else AbSeqIndex(x, g') == AbSeqIndex(x, g)
  {
    Seq_Props_length<AbInt> ();
    g' := AbSeqInit(AbSeqLen(g),
      x requires AbLeqLt(x, I0, AbSeqLen(g)) =>
      if x == p' then index'
      else if AbLt(index, AbSeqIndex(x, g)) then AbAdd(AbSeqIndex(x, g), I1)
      else AbSeqIndex(x, g));
  }

method InsertAfter<X>(l:DList<X>, p:AbInt, a:X) returns(l':DList<X>, p':AbInt)
  requires Inv(l)
  requires MaybePtr(l, p)
  ensures Inv(l')
  ensures AbLeq(I0, AbAdd(Index(l, p), I1)) && AbLeq(AbAdd(Index(l, p), I1), AbSeqLen(Seq(l))) ==> // precond
    Seq(l') == AbSeqInsertIdx(AbAdd(Index(l, p), I1), a, Seq(l))
  ensures ValidPtr(l', p') && Index(l', p') == AbAdd(Index(l, p), I1)
  ensures forall x :: ValidPtr(l, x) ==> ValidPtr(l', x) && if AbLeq(Index(l, x), Index(l, p)) then Index(l', x) == Index(l, x) else Index(l', x) == AbAdd(Index(l, x), I1)
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
  Props_add1sub1_is_orig ();
  Props_pos(I1);
  Props_add_pos_is_lt (); // index < index'
  Props_lt_transitive'_p3 (I0, index, index'); // index' >= 0
  Props_lt2leq_add (); // index' < |s| + 1 ==> index' <= |s|
  /** precond ends */
  ghost var s' := AbSeqInsertIdx(index', a, s);
  ghost var f' := AbSeqInsertIdx(index', p', f);
  ghost var g' := InsertAfter_SeqInit(g, p', index, index');
  var node := AbSeqIndex(p, nodes);
  var node' := Node(Some(a), node.next, p);
  var nodes' := AbSeqUpdate(p, node.(next := p'), nodes);
  var node_next := AbSeqIndex(node.next, nodes');
  var nodes'' := AbSeqUpdate(node.next, node_next.(prev := p'), nodes');
  var nodes''' := AbSeqUpdate(p', node', nodes'');
  l' := DList(nodes''', freeNode.next, s', f', g');

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
  // assert forall i {:trigger AbSeqIndex(i, s')} :: AbLeqLt(i, I0, index') ==> AbSeqIndex(i, s') == AbSeqIndex(i, s);
  Props_lt_transitive'_pxy(I0, index'); // 0 <= index' < ?
  // assert AbLeq(sentinel, index); // index >= sentinel
  Props_lt_transitive'_pxy(sentinel, index); // sentinel <= index < ?
  Props_lt2leq_add_px (sentinel); // ? > sentinel ==> ? >= 0
  Props_lt_subtraction_pya (AbSeqLen(s'), I1);
  // assert forall i {:trigger AbSeqIndex(AbSub(i, I1), s)} :: AbLt(index', i) && AbLt(i, AbSeqLen(s')) ==> AbSeqIndex(AbSub(i, I1), s) == AbSeqIndex(i, s');
  Props_lt_is_not_leq_px (index');
  assert forall i {:trigger AbSeqIndex(i, f')} :: AbLeqLt(i, I0, AbSeqLen(f')) ==> if AbLt(i, index') then AbSeqIndex(i, f') == AbSeqIndex(i, f) else if i == index' then AbSeqIndex(i, f') == p' else AbSeqIndex(i, f') == AbSeqIndex(AbSub(i, I1), f); // trigger
  assert forall i {:trigger AbSeqIndex(i, s')} :: AbLeqLt(i, I0, AbSeqLen(s')) ==> if AbLt(i, index') then AbSeqIndex(i, s') == AbSeqIndex(i, s) else if i == index' then AbSeqIndex(i, s') == a else AbSeqIndex(i, s') == AbSeqIndex(AbSub(i, I1), s); // trigger

  /* 0 <= i < |f| ==> 0 < f[i] < |nodes| */
  // assert (forall i {:trigger AbSeqIndex(i, f')} :: AbLeqLt(i, I0, AbSeqLen(f')) ==> AbLt(I0, AbSeqIndex(i, f')) && AbLt(AbSeqIndex(i, f'), AbSeqLen(nodes''')) );

  /* 0 <= i < |f| ==> g[f[i]] == i */
  Props_lt2leq_sub_py (index'); // ? < index' ==> ? <= index
  Props_lt_subtraction_pxa (index', I1); // ? > index' ==> ?-1 > index
  // assert (forall i {:trigger AbSeqIndex(AbSeqIndex(i, f'), g')} :: AbLeqLt(i, I0, AbSeqLen(f')) ==> AbSeqIndex(AbSeqIndex(i, f'), g') == i );

  /* 0 <= p < |g| ==> unused <= g[p] < |s| */
  Props_lt_transitive'_p3 (unused, I0, index'); // unused < index'
  Props_lt_transitive'_px_add (unused);  // unused < ? < ?+1
  Props_lt_addition_pya (AbSeqLen(s), I1); // ? < |s| ==> ?+1 < |s'|
  Props_lt_transitive'_pyz (index, AbSeqLen(s'));  // ? <= index < |s'|
  // assert (forall p {:trigger AbSeqIndex(p, g')} :: AbLeqLt(p, I0, AbSeqLen(g')) ==> AbLeqLt(AbSeqIndex(p, g'), unused, AbSeqLen(s')) );

  /** precond for Update */
  Props_lt_transitive'_pyz (p, AbSeqLen(nodes)); // ? < p < |nodes|
  Props_lt_transitive'_pxy (I0, p); // I0 < p < ?
  Props_lt_transitive'_pyz (node.next, AbSeqLen(nodes)); // ? < node.next < |nodes|
  Props_lt_transitive'_pxy (I0, node.next); // I0 < node.next < ?
  Props_lt_transitive'_pyz (p', AbSeqLen(nodes)); // ? < p' < |nodes|
  Props_lt_transitive'_pxy (I0, p'); // I0 < p' < ?
  // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes')} :: AbLeqLt(i, I0, p) ==> AbSeqIndex(i, nodes) == AbSeqIndex(i, nodes'));
  // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes)} :: AbLtLt(i, p, AbSeqLen(nodes')) ==> AbSeqIndex(i, nodes) == AbSeqIndex(i, nodes'));
  // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes'')} :: AbLeqLt(i, I0, node.next) ==> AbSeqIndex(i, nodes') == AbSeqIndex(i, nodes''));
  // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes'')} :: AbLtLt(i, node.next, AbSeqLen(nodes'')) ==> AbSeqIndex(i, nodes') == AbSeqIndex(i, nodes''));
  // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes''')} :: AbLeqLt(i, I0, p') ==> AbSeqIndex(i, nodes'') == AbSeqIndex(i, nodes'''));
  // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes''')} :: AbLtLt(i, p', AbSeqLen(nodes''')) ==> AbSeqIndex(i, nodes'') == AbSeqIndex(i, nodes'''));

  /* 0 <= p < |g| ==> 0 <= nodes[p].next < |g| */
  Props_lt_is_not_leq_px (p);
  Props_lt_is_not_leq_px (node.next);
  Props_lt_is_not_leq_px (p');
  // assert (forall p {:trigger AbSeqIndex(p, nodes''').next} :: AbLeqLt(p, I0, AbSeqLen(g')) ==> AbLeqLt(AbSeqIndex(p, nodes''').next, I0, AbSeqLen(g')) );

  /* 0 <= p < |g| ==> (g[p] >= 0 <==> nodes[p].data.Some?) */
  // assert (forall p {:trigger AbSeqIndex(p, nodes''').data} :: AbLeqLt(p, I0, AbSeqLen(g')) ==> (AbLeq(I0, AbSeqIndex(p, g')) <==> AbSeqIndex(p, nodes''').data.Some?) );

  /* 0 <= p < |g| && sentinel <= g[p] ==> (g[p] == sentinel ==> p == 0) */
  // assert (forall p {:trigger AbSeqIndex(p, g')} :: AbLeqLt(p, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(p, g')) ==> (AbSeqIndex(p, g') == sentinel ==> p == I0) );

  /* 0 <= p < |g| && sentinel <= g[p] ==> (0 <= g[p] ==> f[g[p]] == p && nodes[p].data == Some(s[g[p]])) */
  // Props_lt_transitive'_pxy (sentinel, I0);
  Props_leq2lt_sub_py (index);
  // assert (forall p {:trigger AbSeqIndex(AbSeqIndex(p, g'), f')} :: AbLeqLt(p, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(p, g')) ==> (AbLeq(I0, AbSeqIndex(p, g')) ==> AbSeqIndex(AbSeqIndex(p, g'), f') == p));
  // assert forall i {:trigger AbSeqIndex(i, s')} :: AbLeqLt(i, I0, AbSeqLen(s')) ==> if AbLt(i, index') then AbSeqIndex(i, s') == AbSeqIndex(i, s) else if i == index' then AbSeqIndex(i, s') == a else AbSeqIndex(i, s') == AbSeqIndex(AbSub(i, I1), s); // InsertIdx trigger
  // assert (forall p {:trigger AbSeqIndex(AbSeqIndex(p, g'), s')} :: AbLeqLt(p, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(p, g')) ==> (AbLeq(I0, AbSeqIndex(p, g')) ==> AbSeqIndex(p, nodes''').data == Some(AbSeqIndex(AbSeqIndex(p, g'), s'))) );

  /* 0 <= p < |g| && sentinel <= g[p] ==> nodes[p].next == (if g[p] + 1 < |f| then f[g[p] + 1] else 0) */
  Props_lt_addition_pxa (sentinel, I1); // sentinel < ? ==> 0 < ?+1
  // assert (forall i {:trigger AbSeqIndex(i, nodes''').next} :: AbLeqLt(i, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(i, g')) ==> (if AbLt(AbAdd(AbSeqIndex(i, g'), I1), AbSeqLen(f')) then AbSeqIndex(i, nodes''').next == AbSeqIndex(AbAdd(AbSeqIndex(i, g'), I1), f') else AbSeqIndex(i, nodes''').next == I0 ) );
  
  /* 0 <= p < |g| && sentinel <= g[p] ==> nodes[p].prev == (if g[p] > 0 then f[g[p] - 1] else if g[p] == 0 || |f| == 0 then 0 else f[|f| - 1]) */
  Props_lt_addition_pya (index, I1); // index < ? ==> index' < ?+1
  // assert (forall p {:trigger AbSeqIndex(p, nodes''').prev} :: AbLeqLt(p, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(p, g')) ==> if AbLt(I0, AbSeqIndex(p, g')) then AbLeq(I0, AbSub(AbSeqIndex(p, g'), I1)) ==> AbLt(AbSub(AbSeqIndex(p, g'), I1), AbSeqLen(f')) ==> AbSeqIndex(p, nodes''').prev == AbSeqIndex(AbSub(AbSeqIndex(p, g'), I1), f') else if I0 == AbSeqIndex(p, g') || I0 == AbSeqLen(f') then AbSeqIndex(p, nodes''').prev == I0 else AbLeq(I0, AbSub(AbSeqLen(f'), I1)) ==> AbLt(AbSub(AbSeqLen(f'), I1), AbSeqLen(f')) ==> AbSeqIndex(p, nodes''').prev == AbSeqIndex(AbSub(AbSeqLen(f'), I1), f') );
}

ghost method InsertBefore_SeqInit(g: AbSeq<AbInt>, p': AbInt, index': AbInt) returns (g': AbSeq<AbInt>)
  ensures AbSeqLen(g') == AbSeqLen(g)
  ensures forall x {:trigger AbSeqIndex(x, g')} {:trigger AbSeqIndex(x, g)} ::
    AbLeqLt(x, I0, AbSeqLen(g)) ==>
      if x == p' then AbSeqIndex(x, g') == index'
      else if AbLeq(index', AbSeqIndex(x, g)) then AbSeqIndex(x, g') == AbAdd(AbSeqIndex(x, g), I1)
      else AbSeqIndex(x, g') == AbSeqIndex(x, g)
  {
    Seq_Props_length<AbInt> ();
    g' := AbSeqInit(AbSeqLen(g),
      x requires AbLeqLt(x, I0, AbSeqLen(g)) =>
        if x == p' then index'
        else if AbLeq(index', AbSeqIndex(x, g)) then AbAdd(AbSeqIndex(x, g), I1)
        else AbSeqIndex(x, g));
  }

method InsertBefore<A>(l:DList<A>, p:AbInt, a:A) returns(l':DList<A>, p':AbInt)
  requires Inv(l)
  requires MaybePtr(l, p) // p == 0 || (0 < p < |g| && g[p] >= 0)
  ensures Inv(l')
  ensures AbLeq(I0, IndexHi(l, p)) && AbLeq(IndexHi(l, p), AbSeqLen(Seq(l))) ==> // precond
    Seq(l') == AbSeqInsertIdx(IndexHi(l, p), a, Seq(l))
  ensures ValidPtr(l', p') && Index(l', p') == IndexHi(l, p)
  ensures forall x :: ValidPtr(l, x) ==> ValidPtr(l', x) && if AbLt(Index(l, x), IndexHi(l, p)) then Index(l', x) == Index(l, x) else Index(l', x) == AbAdd(Index(l, x), I1)
{
  var l_exp := l;
  p' := l_exp.freeStack;
  var freeNode := AbSeqIndex(p', l_exp.nodes);
  if (p' == I0 || freeNode.data.Some?) {
    l_exp := Expand(l_exp);
    p' := l_exp.freeStack; // 0 <= p' < |nodes|
    freeNode := AbSeqIndex(p', l_exp.nodes);
  }
  var DList(nodes, freeStack, s, f, g) := l_exp;
  assert ValidPtr(l, p) ==> ValidPtr(l_exp, p); // trigger
  ghost var index' := IndexHi(l, p); // index' == |s| || index' == g[p] (>= 0)
  Seq_Props_length<AbInt> (); // |s| >= 0
  ghost var s' := AbSeqInsertIdx(index', a, s);
  ghost var f' := AbSeqInsertIdx(index', p', f);
  ghost var g' := InsertBefore_SeqInit(g, p', index');
  var node := AbSeqIndex(p, nodes);
  var node' := Node(Some(a), p, node.prev);
  var nodes' := AbSeqUpdate(p, node.(prev := p'), nodes);
  /** precond for AbSeqIndex */
  Props_lt2leq_sub_px (I0); // 0 < ? ==> 0 <= ?-1
  Props_pos(I1);
  Props_add_pos_is_lt (); // ? < ? + 1
  Props_add1sub1_is_orig ();
  Props_lt_transitive'_pxy(sentinel, I0); // sentinel < 0 < ?
  Props_lt_transitive'_pz_add (AbSeqLen(f)); // ?-1 < ? < |f|
  // assert AbLeq(I0, node.prev);
  // assert AbLt(node.prev, AbSeqLen(nodes));
  /** precond ends */
  var node_prev := AbSeqIndex(node.prev, nodes');
  var nodes'' := AbSeqUpdate(node.prev, node_prev.(next := p'), nodes');
  var nodes''' := AbSeqUpdate(p', node', nodes'');
  l' := DList(nodes''', freeNode.next, s', f', g');

  /** ValidPtr(l', p') && Index(l', p') == IndexHi(l, p) */

  /** forall x :: ValidPtr(l, x) ==> ValidPtr(l', x) && Index(l', x) == Index(l, x) + (if Index(l, x) < IndexHi(l, p) then 0 else 1) */
  assert forall x {:trigger ValidPtr(l, x)} :: ValidPtr(l, x) ==> ValidPtr(l_exp, x); // trigger
  Props_lt_transitive'_px_add(I0);

  /* check Inv(l') */
  /** g[0] == sentinel */
  Props_lt_is_not_leq_px (index');

  /** postcond for InsertIdx */
  Props_lt_transitive'_pyz(index', AbSeqLen(s)); // ? < index' <= |s|
  Props_lt_transitive'_p3(index', AbSeqLen(s), AbSeqLen(s'));
  Props_lt_transitive'_pyz(index', AbSeqLen(s')); // ? < index' < |s'|
  // assert forall i {:trigger AbSeqIndex(i, s')} :: AbLeqLt(i, I0, index') ==> AbSeqIndex(i, s') == AbSeqIndex(i, s);
  Props_lt_transitive'_pxy(I0, index'); // 0 <= index' < ?, 0 <= ?-1
  Props_lt_subtraction_pya (AbSeqLen(s'), I1);
  // assert forall i {:trigger AbSeqIndex(AbSub(i, I1), s)} :: AbLt(index', i) && AbLt(i, AbSeqLen(s')) ==> AbSeqIndex(AbSub(i, I1), s) == AbSeqIndex(i, s');
  assert forall i {:trigger AbSeqIndex(i, f')} :: AbLeqLt(i, I0, AbSeqLen(f')) ==> if AbLt(i, index') then AbSeqIndex(i, f') == AbSeqIndex(i, f) else if i == index' then AbSeqIndex(i, f') == p' else AbSeqIndex(i, f') == AbSeqIndex(AbSub(i, I1), f); // trigger
  assert forall i {:trigger AbSeqIndex(i, s')} :: AbLeqLt(i, I0, AbSeqLen(s')) ==> if AbLt(i, index') then AbSeqIndex(i, s') == AbSeqIndex(i, s) else if i == index' then AbSeqIndex(i, s') == a else AbSeqIndex(i, s') == AbSeqIndex(AbSub(i, I1), s); // trigger

  /* 0 <= i < |f| ==> 0 < f[i] < |nodes| */
  // assert (forall i {:trigger AbSeqIndex(i, f')} :: AbLeqLt(i, I0, AbSeqLen(f')) ==> AbLt(I0, AbSeqIndex(i, f')) && AbLt(AbSeqIndex(i, f'), AbSeqLen(nodes''')) );

  /* 0 <= i < |f| ==> g[f[i]] == i */
  Props_lt_subtraction_pxa (index', I1); // ? > index' ==> ?-1 > index'-1
  Props_lt2leq_add_px (AbSub(index', I1)); // ? > index'-1 ==> ? >= index'
  // assert (forall i {:trigger AbSeqIndex(AbSeqIndex(i, f'), g')} :: AbLeqLt(i, I0, AbSeqLen(f')) ==> AbSeqIndex(AbSeqIndex(i, f'), g') == i );

  /* 0 <= p < |g| ==> unused <= g[p] < |s| */
  Props_lt_transitive'_p3 (unused, I0, index'); // unused < index'
  Props_lt_transitive'_px_add (unused);  // unused < ? < ?+1
  Props_lt_addition_pya (AbSeqLen(s), I1); // ? < |s| ==> ?+1 < |s'|
  // assert (forall p {:trigger AbSeqIndex(p, g')} :: AbLeqLt(p, I0, AbSeqLen(g')) ==> AbLeqLt(AbSeqIndex(p, g'), unused, AbSeqLen(s')) );

  /** precond for Update */
  Props_lt_transitive'_pyz (p, AbSeqLen(nodes)); // ? < p < |nodes|
  Props_lt_transitive'_pxy (I0, p); // I0 < p < ?
  Props_lt_transitive'_pyz (node.prev, AbSeqLen(nodes)); // ? < node.prev < |nodes|
  Props_lt_transitive'_pxy (I0, node.prev); // I0 < node.prev < ?
  Props_lt_transitive'_pyz (p', AbSeqLen(nodes)); // ? < p' < |nodes|
  Props_lt_transitive'_pxy (I0, p'); // I0 < p' < ?
  // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes')} :: AbLeqLt(i, I0, p) ==> AbSeqIndex(i, nodes) == AbSeqIndex(i, nodes'));
  // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes)} :: AbLtLt(i, p, AbSeqLen(nodes')) ==> AbSeqIndex(i, nodes) == AbSeqIndex(i, nodes'));
  // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes'')} :: AbLeqLt(i, I0, node.prev) ==> AbSeqIndex(i, nodes') == AbSeqIndex(i, nodes''));
  // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes'')} :: AbLtLt(i, node.prev, AbSeqLen(nodes'')) ==> AbSeqIndex(i, nodes') == AbSeqIndex(i, nodes''));
  // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes''')} :: AbLeqLt(i, I0, p') ==> AbSeqIndex(i, nodes'') == AbSeqIndex(i, nodes'''));
  // assert (forall i : AbInt {:trigger AbSeqIndex(i, nodes''')} :: AbLtLt(i, p', AbSeqLen(nodes''')) ==> AbSeqIndex(i, nodes'') == AbSeqIndex(i, nodes'''));

  /* 0 <= p < |g| ==> 0 <= nodes[p].next < |g| */
  Props_lt_is_not_leq_px (p);
  Props_lt_is_not_leq_px (node.prev);
  Props_lt_is_not_leq_px (p');
  // assert (forall p {:trigger AbSeqIndex(p, nodes''').next} :: AbLeqLt(p, I0, AbSeqLen(g')) ==> AbLeqLt(AbSeqIndex(p, nodes''').next, I0, AbSeqLen(g')) );

  /* 0 <= p < |g| ==> (g[p] >= 0 <==> nodes[p].data.Some?) */
  // assert (forall p {:trigger AbSeqIndex(p, nodes''').data} :: AbLeqLt(p, I0, AbSeqLen(g')) ==> (AbLeq(I0, AbSeqIndex(p, g')) <==> AbSeqIndex(p, nodes''').data.Some?) );

  /* 0 <= p < |g| && sentinel <= g[p] ==> (g[p] == sentinel ==> p == 0) */
  // assert (forall p {:trigger AbSeqIndex(p, g')} :: AbLeqLt(p, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(p, g')) ==> (AbSeqIndex(p, g') == sentinel ==> p == I0) );

  /* 0 <= p < |g| && sentinel <= g[p] ==> (0 <= g[p] ==> f[g[p]] == p && nodes[p].data == Some(s[g[p]])) */
  Props_leq2lt_add_px (index'); // index' <= ? -> index' < ?+1
  // assert (forall p {:trigger AbSeqIndex(AbSeqIndex(p, g'), f')} :: AbLeqLt(p, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(p, g')) ==> (AbLeq(I0, AbSeqIndex(p, g')) ==> AbSeqIndex(AbSeqIndex(p, g'), f') == p));
  // assert forall i {:trigger AbSeqIndex(i, s')} :: AbLeqLt(i, I0, AbSeqLen(s')) ==> if AbLt(i, index') then AbSeqIndex(i, s') == AbSeqIndex(i, s) else if i == index' then AbSeqIndex(i, s') == a else AbSeqIndex(i, s') == AbSeqIndex(AbSub(i, I1), s); // InsertIdx trigger
  // assert (forall p {:trigger AbSeqIndex(AbSeqIndex(p, g'), s')} :: AbLeqLt(p, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(p, g')) ==> (AbLeq(I0, AbSeqIndex(p, g')) ==> AbSeqIndex(p, nodes''').data == Some(AbSeqIndex(AbSeqIndex(p, g'), s'))) );

  /* 0 <= p < |g| && sentinel <= g[p] ==> nodes[p].next == (if g[p] + 1 < |f| then f[g[p] + 1] else 0) */
  Props_lt_addition_pxa (sentinel, I1); // sentinel < ? ==> 0 < ?+1
  // assert (forall i {:trigger AbSeqIndex(i, nodes''').next} :: AbLeqLt(i, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(i, g')) ==> (if AbLt(AbAdd(AbSeqIndex(i, g'), I1), AbSeqLen(f')) then AbSeqIndex(i, nodes''').next == AbSeqIndex(AbAdd(AbSeqIndex(i, g'), I1), f') else AbSeqIndex(i, nodes''').next == I0 ) );
  
  /* 0 <= p < |g| && sentinel <= g[p] ==> nodes[p].prev == (if g[p] > 0 then f[g[p] - 1] else if g[p] == 0 || |f| == 0 then 0 else f[|f| - 1]) */
  // assert (forall p {:trigger AbSeqIndex(p, nodes''').prev} :: AbLeqLt(p, I0, AbSeqLen(g')) && AbLeq(sentinel, AbSeqIndex(p, g')) ==> if AbLt(I0, AbSeqIndex(p, g')) then AbLeq(I0, AbSub(AbSeqIndex(p, g'), I1)) ==> AbLt(AbSub(AbSeqIndex(p, g'), I1), AbSeqLen(f')) ==> AbSeqIndex(p, nodes''').prev == AbSeqIndex(AbSub(AbSeqIndex(p, g'), I1), f') else if I0 == AbSeqIndex(p, g') || I0 == AbSeqLen(f') then AbSeqIndex(p, nodes''').prev == I0 else AbLeq(I0, AbSub(AbSeqLen(f'), I1)) ==> AbLt(AbSub(AbSeqLen(f'), I1), AbSeqLen(f')) ==> AbSeqIndex(p, nodes''').prev == AbSeqIndex(AbSub(AbSeqLen(f'), I1), f') );
}

method Clone<A>(l:DList<A>) returns(l':DList<A>)
  ensures l' == l
{
  var DList(nodes, freeStack, s, f, g) := l;
  Seq_Props_length<Node<A>> ();
  var nodes' := AbSeqSlice(I0, AbSeqLen(nodes), nodes);
  Props_sub_identity ();
  Seq_Props_Equivalent<Node<A>> (nodes, nodes');
  l' := DList(nodes', freeStack, s, f, g);
}

const I3 : AbInt := AbAdd(I2, I1)
const I4 : AbInt := AbAdd(I3, I1)
const I5 : AbInt := AbAdd(I4, I1)
const I6 : AbInt := AbAdd(I5, I1)

function method check_main_seq1 (s: AbSeq<AbInt>): (b: bool)
  ensures b == ( AbSeqLen(s) == I5 && 
    (AbLt(I0, I5) ==> AbSeqIndex(I0, s) == I2A(100)) &&
    (AbLeqLt(I1, I0, I5) ==> AbSeqIndex(I1, s) == I2A(200)) &&
    (AbLeqLt(I2, I0, I5) ==> AbSeqIndex(I2, s) == I2A(300)) &&
    (AbLeqLt(I3, I0, I5) ==> AbSeqIndex(I3, s) == I2A(400)) &&
    (AbLeqLt(I4, I0, I5) ==> AbSeqIndex(I4, s) == I2A(500)) )

function method check_main_seq2 (s: AbSeq<AbInt>): (b: bool)
  ensures b == ( AbSeqLen(s) == I4 &&
    (AbLt(I0, I4) ==> AbSeqIndex(I0, s) == I2A(100)) &&
    (AbLeqLt(I1, I0, I4) ==> AbSeqIndex(I1, s) == I2A(200)) &&
    (AbLeqLt(I2, I0, I4) ==> AbSeqIndex(I2, s) == I2A(400)) &&
    (AbLeqLt(I3, I0, I4) ==> AbSeqIndex(I3, s) == I2A(500)) )

function method check_main_seq3 (s: AbSeq<AbInt>): (b: bool)
  ensures b == ( AbSeqLen(s) == I6 &&
    (AbLt(I0, I6) ==> AbSeqIndex(I0, s) == I2A(100)) &&
    (AbLeqLt(I1, I0, I6) ==> AbSeqIndex(I1, s) == I2A(200)) &&
    (AbLeqLt(I2, I0, I6) ==> AbSeqIndex(I2, s) == I2A(400)) &&
    (AbLeqLt(I3, I0, I6) ==> AbSeqIndex(I3, s) == I2A(500)) &&
    (AbLeqLt(I4, I0, I6) ==> AbSeqIndex(I4, s) == I2A(600)) &&
    (AbLeqLt(I5, I0, I6) ==> AbSeqIndex(I5, s) == I2A(700)) )

// ~ 1500s
method main()
{
  Props_pos(I1);
  Props_add_pos_is_lt ();
  Props_2is1add1 ();
  Props_lt_transitive'();
  var l := Alloc<AbInt>(I3);
  var p;

  Props_add1sub1_is_orig ();
  Props_add_identity ();
  Props_lt2leq_add ();

  assume AbLt(I0, I2A(100));
  assume AbLt(I2A(100), I2A(200));
  assume AbLt(I2A(200), I2A(300));
  assume AbLt(I2A(300), I2A(400));
  assume AbLt(I2A(400), I2A(500));
  assume AbLt(I2A(500), I2A(600));
  assume AbLt(I2A(600), I2A(700));

  l, p := InsertAfter(l, I0, I2A(100));
  l, p := InsertAfter(l, p, I2A(200));
  l, p := InsertAfter(l, p, I2A(300));
  var p3 := p;
  l, p := InsertAfter(l, p, I2A(400));
  l, p := InsertAfter(l, p, I2A(500));
  assert check_main_seq1 (Seq(l));

  l := Remove(l, p3);
  assert check_main_seq2 (Seq(l));

  l, p := InsertAfter(l, p, I2A(600));
  l, p := InsertAfter(l, p, I2A(700));
  assert check_main_seq3 (Seq(l));
  Free(l);
}
