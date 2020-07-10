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
  && AbLeqLt(freeStack, I0, AbSeqLen(nodes))
  && (forall i {:trigger AbSeqIndex(i, f)} ::
    // 0 <= i < |f| ==> 0 < f[i] < |nodes|
    AbLeqLt(i, I0, AbSeqLen(f)) ==> AbLtLt(AbSeqIndex(i, f), I0, AbSeqLen(nodes)) )
  && (forall i {:trigger AbSeqIndex(AbSeqIndex(i, f), g)} ::
    // 0 <= i < |f| ==> g[f[i]] == i
    AbLeqLt(i, I0, AbSeqLen(f)) ==> AbSeqIndex(AbSeqIndex(i, f), g) == i )
  && (forall p {:trigger AbSeqIndex(p, g)} ::
    // 0 <= p < |g| ==> unused <= g[p] < |s|
    AbLeqLt(p, I0, AbSeqLen(g)) ==> AbLeqLt(AbSeqIndex(p, g), unused, AbSeqLen(s)) )
  && (forall p {:trigger AbSeqIndex(p, nodes).next} ::
    // 0 <= p < |g| ==> 0 <= nodes[p].next < |g|
    AbLeqLt(p, I0, AbSeqLen(g)) ==> AbLeqLt(AbSeqIndex(p, nodes).next, I0, AbSeqLen(g)) )
  && (forall p {:trigger AbSeqIndex(p, g)} {:trigger AbSeqIndex(p, nodes).data} ::
    // 0 <= p < |g| ==> (g[p] >= 0 <==> nodes[p].data.Some?)
    AbLeqLt(p, I0, AbSeqLen(g)) ==> (AbLeq(I0, AbSeqIndex(p, g)) <==> AbSeqIndex(p, nodes).data.Some?) )
  && (forall p {:trigger AbSeqIndex(p, g)} ::
    // 0 <= p < |g| && sentinel <= g[p] ==> (g[p] == sentinel ==> p == 0)
    AbLeqLt(p, I0, AbSeqLen(g)) && AbLeq(sentinel, AbSeqIndex(p, g)) ==> (AbSeqIndex(p, g) == sentinel ==> p == I0) )
  && (forall p {:trigger AbSeqIndex(p, g)} {:trigger AbSeqIndex(AbSeqIndex(p, g), f)} {:trigger AbSeqIndex(AbSeqIndex(p, g), s)} ::
    // 0 <= p < |g| && sentinel <= g[p] ==> (0 <= g[p] ==> f[g[p]] == p && nodes[p].data == Some(s[g[p]]))
    AbLeqLt(p, I0, AbSeqLen(g)) && AbLeq(sentinel, AbSeqIndex(p, g)) ==>
      (AbLeq(I0, AbSeqIndex(p, g)) ==>
        AbSeqIndex(AbSeqIndex(p, g), f) == p &&
        AbSeqIndex(p, nodes).data == Some(AbSeqIndex(AbSeqIndex(p, g), s))) )
  && (forall p {:trigger AbSeqIndex(p, g)} {:trigger AbSeqIndex(p, nodes).next} ::
    AbLeqLt(p, I0, AbSeqLen(g)) && AbLeq(sentinel, AbSeqIndex(p, g)) ==>
      // 0 <= p < |g| && sentinel <= g[p] ==> nodes[p].next == (if g[p] + 1 < |f| then f[g[p] + 1] else 0)
      (if AbLt(AbAdd(AbSeqIndex(p, g), I1), AbSeqLen(f)) then
        AbLeq(I0, AbAdd(AbSeqIndex(p, g), I1)) ==> // precond: 0 <= g[p]+1
        AbSeqIndex(p, nodes).next == AbSeqIndex(AbAdd(AbSeqIndex(p, g), I1), f) // nonlast.next or sentinel.next
      else AbSeqIndex(p, nodes).next == I0 ) ) // last.next == sentinel or sentinel.next == sentinel
  && (forall p {:trigger AbSeqIndex(p, g)} {:trigger AbSeqIndex(p, nodes).prev} ::
    AbLeqLt(p, I0, AbSeqLen(g)) && AbLeq(sentinel, AbSeqIndex(p, g)) ==>
      // 0 <= p < |g| && sentinel <= g[p] ==> nodes[p].prev == (if g[p] > 0 then f[g[p] - 1] else if g[p] == 0 || |f| == 0 then 0 else f[|f| - 1])
      if AbLt(I0, AbSeqIndex(p, g)) then
        AbLeq(I0, AbSub(AbSeqIndex(p, g), I1)) ==> // precond: 0 <= index
        AbLt(AbSub(AbSeqIndex(p, g), I1), AbSeqLen(f)) ==> // precond: index < |f|
        AbSeqIndex(p, nodes).prev == AbSeqIndex(AbSub(AbSeqIndex(p, g), I1), f) // nonfirst.prev
      else if I0 == AbSeqIndex(p, g) || I0 == AbSeqLen(f) then
        AbSeqIndex(p, nodes).prev == I0 // first.prev == sentinel or sentinel.prev == sentinel
      else
        AbLeq(I0, AbSub(AbSeqLen(f), I1)) ==> // precond: 0 <= index
        AbLt(AbSub(AbSeqLen(f), I1), AbSeqLen(f)) ==> // precond: index < |f|
        AbSeqIndex(p, nodes).prev == AbSeqIndex(AbSub(AbSeqLen(f), I1), f) ) // sentinel.prev == last
}

predicate Inv<A>(l:DList<A>) { Invs(l.nodes, l.freeStack, l.s, l.f, l.g) }

function Seq<A>(l:DList<A>): AbSeq<A> { l.s }

function ValidPtr<A>(l:DList<A>, p:AbInt):(b:bool)
  ensures b ==> p != I0
  {
    // 0 < p < |l.g| && l.g[p] >= 0
    Props_lt_is_not_leq ();
    AbLtLt(p, I0, AbSeqLen(l.g)) && AbLeq(I0, AbSeqIndex(p, l.g))
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
  ensures Inv(l')
  ensures Seq(l') == AbSeqRemoveIdx(Index(l, p), Seq(l))
  ensures forall x :: x != p && ValidPtr(l, x) ==> ValidPtr(l', x) && ( if AbLt(Index(l, x), Index(l, p)) then Index(l', x) == Index(l, x) else Index(l', x) == AbSub(Index(l, x), I1) )
  {
    var DList(nodes, freeStack, s, f, g) := l;
    ghost var index := AbSeqIndex(p, g);
    ghost var s' := AbSeqRemoveIdx(index, s); // s[.. index] + s[index + 1 ..];
    ghost var f' := AbSeqRemoveIdx(index, f); // f[.. index] + f[index + 1 ..];
    Seq_Props_length<AbInt> (); // AbSeqLen(g/f) >= 0
    ghost var g' := AbSeqInit(AbSeqLen(g), // len >= 0
      x requires AbLeqLt(x, I0, AbSeqLen(g)) =>
      if AbSeqIndex(x, g) == index then unused
      else if AbLt(index, AbSeqIndex(x, g)) then AbSub(AbSeqIndex(x, g), I1)
      else AbSeqIndex(x, g) );
    /*** precond for AbSeqIndex(node.prev, nodes) */
    Props_leq2lt_sub_p2 (I0, index);
    // assert AbLeq(sentinel, index); // true
    // Props_lt_is_not_leq_p2 (I0, index); 
    // assert !AbLt(index, I0);
    Props_lt_is_not_leq_px (index);
    // Props_lt_is_not_leq_py (index);
    Props_lt_is_not_leq_px (I0);
    Props_lt_is_not_leq_py (AbSeqLen(f));
    Props_lt_is_not_leq_py (AbSeqLen(f'));
    // Props_lt_is_not_leq ();
    Props_lt2leq_sub ();
    // assert AbLt(I0, index) ==> AbLeq(I0, AbSub(index, I1)); // true
    // assert AbLt(index, AbSeqLen(f)); // true
    Props_pos(I1);
    Props_add_sub_is_orig (); // Props_add_sub_is_orig_p2 (index, I1);
    Props_lt_add_notneg (); // Props_lt_add_notneg_p3 (AbSub(index, I1), AbSeqLen(f), I1);
    // assert AbLt(AbSub(index, I1), AbSeqLen(f)); // true
    // assert AbLeq(I0, node.prev); // true
    // assert AbLt(node.prev, AbSeqLen(nodes)); // true
    /*** precond ends */
    var node := AbSeqIndex(p, nodes);
    var node_prev := AbSeqIndex(node.prev, nodes);
    var nodes' := AbSeqUpdate(node.prev, node_prev.(next := node.next), nodes);
    // assert AbSeqIndex(node.prev, nodes').next == node.next;
    var node_next := AbSeqIndex(node.next, nodes');
    // assert if node.next != node.prev then AbSeqIndex(node.next, nodes').next == AbSeqIndex(node.next, nodes).next else true;
    var nodes'' := AbSeqUpdate(node.next, node_next.(prev := node.prev), nodes');
    // assert AbSeqIndex(node.prev, nodes'').next == node.next;
    var nodes''' := AbSeqUpdate(p, Node(None, freeStack, I0), nodes'');

    Props_lt_is_not_leq_px (node.prev);
    Props_lt_is_not_leq_py (node.prev);
    Props_lt_is_not_leq_px (node.next);
    Props_lt_is_not_leq_py (node.next);
    Props_lt_is_not_leq_px (p);
    Props_lt_is_not_leq_py (p);

    l' := DList(nodes''', p, s', f', g');
    
    // assert forall x {:trigger AbSeqIndex(x, l'.g)} :: x != p && ValidPtr(l, x) ==> ValidPtr(l', x); // true
    // assert forall x {:trigger AbSeqIndex(x, l'.g)} :: x != p && ValidPtr(l, x) ==>
    //   ( if AbLt(Index(l, x), Index(l, p)) 
    //     then Index(l', x) == Index(l, x)
    //     else Index(l', x) == AbSub(Index(l, x), I1) );

    /* check Inv(l') */
    Props_add_pos_is_lt ();
    // assert AbSeqLen(f') == AbSeqLen(s'); // true
    // assert AbSeqLen(g') == AbSeqLen(nodes); // true
    // assert AbLt(I0, AbSeqLen(nodes)); // true
    // assert AbLeq(I0, index); // true
    // assert AbSeqIndex(I0, g') == sentinel; // true
    // assert AbLeqLt(p, I0, AbSeqLen(nodes''')); // true

    Props_lt_transitive ();
    Props_lt_addition ();
    Props_lt2leq_sub_p2(index, AbSeqLen(f));
    /** test for RemoveIdx postcond */
    // assert (forall i : AbInt {:trigger AbSeqIndex(i, f')} :: AbLeqLt(i, I0, index) ==> AbSeqIndex(i, f) == AbSeqIndex(i, f'));    
    // assert (forall i : AbInt {:trigger AbSeqIndex(AbAdd(i, I1), f)} {:trigger AbSeqIndex(i, f')} :: AbLeqLt(i, index, AbSeqLen(f')) ==> AbSeqIndex(AbAdd(i, I1), f) == AbSeqIndex(i, f'));

    // // 0 <= i < |f| ==> 0 < f[i] < |nodes|
    // assert (forall i {:trigger AbSeqIndex(i, f')} :: AbLeqLt(i, I0, AbSeqLen(f')) ==> AbLtLt(AbSeqIndex(i, f'), I0, AbSeqLen(nodes''')) );

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
  requires AbLeq(k, AbSeqLen(a))
  ensures AbSeqLen(b) == AbSeqLen(a)
  ensures forall i :: AbLeqLt(i, I0, k) ==>
    AbLt(i, AbSeqLen(a)) ==> // precond: lt_transitive
    AbSeqIndex(i, b) == AbSeqIndex(i, a)
  ensures forall i :: AbLeqLt(i, k, AbSeqLen(a)) ==>
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
    var b' := AbSeqUpdate(n, Node(None, AbSub(n, I1), I0), b);
    AbSeqUpdate_Part1Same (n, Node(None, AbSub(n, I1), I0), b, b');
    AbSeqUpdate_Part2Same (n, Node(None, AbSub(n, I1), I0), b, b');
    /** AbLeq(n, AbSeqLen(b)) */
    // Props_lt2leq_add_p2 (n, AbSeqLen(b'));
    Props_lt2leq_add ();

    /** AbLeqLt(i, I0, k) ==> AbSeqIndex(i, b) == AbSeqIndex(i, a) */
    Props_lt_transitive();
    // forall i : AbInt | AbLt(i, k) ensures AbLt(i, AbSeqLen(a)) { }

    /** AbLeqLt(i, k, n) ==> AbSeqIndex(i, b) == Node(None, AbSub(i, I1), I0) */
    Props_lt2leq_sub ();
    Props_add_sub_is_orig ();
    // forall i | AbLeqLt(i, k, n) ensures AbLt(I0, i) && AbLt(i, AbSeqLen(b')) { }
    // forall i | AbLeqLt(i, k, AbAdd(n, I1)) ensures AbLt(I0, i) && AbLt(i, AbSeqLen(b')) { }
    // forall i | AbLt(i, AbAdd(n, I1)) ensures AbLeq(i, n)
    //   { Props_lt2leq_sub_p2 (i, AbAdd(n, I1));
    //     Props_add_sub_is_orig_p2 (n, I1); }

    // decreases
    Props_sub_add_is_sub(); // x - (y + 1) == x - y - 1
    Props_pos(I1); // 1 > 0
    Props_add_pos_is_lt (); // x < x + 1
    // Props_add_sub_is_orig (); // (x - 1) + 1 == x
    Props_adt_dt_lt (AbSub(AbSeqLen(b'), AbAdd(n, I1)), AbSub(AbSeqLen(b'), n));

    n := AbAdd(n, I1);
    b := b';
  }
}

method Expand<X> (l:DList<X>) returns (l':DList<X>)
  requires Inv(l)
  ensures Inv(l') // error
  ensures l'.s == l.s
  ensures forall x {:trigger AbSeqIndex(x, l'.g)} :: ValidPtr(l, x) ==> 
    ValidPtr(l', x) && AbSeqIndex(x, l'.g) == AbSeqIndex(x, l.g)
  ensures l'.freeStack != I0 && AbSeqIndex(l'.freeStack, l'.nodes).data.None?
{
  var DList(nodes, freeStack, s, f, g) := l;
  var len := AbSeqLen(nodes); // len > 0
  var len' := AbAdd(len, len);
  var nodes' := AbSeqResize(nodes, len', Node(None, freeStack, I0));

  Props_pos(I1);
  Props_add_pos_is_lt(); // len < len + 1, len < len'
  Props_lt_transitive' ();
  // Props_lt_transitive'_p3(I0, len, len'); // 0 < len'
  Props_lt2leq_add_p2(I0, len);
  Props_add_identity (); // 1 <= len
  Props_add_commutative ();
  Props_lt_addition (); // len + 1 <= len + len = len'
  // Props_lt_transitive'_p3(I0, len, AbAdd(len, I1));
  nodes' := BuildFreeStack(nodes', AbAdd(len, I1));

  Seq_Props_length<Node<X>> ();
  ghost var g' := AbSeqInit( AbSeqLen(nodes'),
    i requires AbLeqLt(i, I0, AbSeqLen(nodes')) =>
      if AbLt(i, AbSeqLen(g)) then AbSeqIndex(i, g) else unused );
  l' := DList(nodes', AbSub(len', I1), s, f, g');

  // Props_lt_transitive'_pyz (len, len');
  // assert forall x : AbInt {:trigger AbSeqIndex(x, l'.g)} :: ValidPtr(l, x) ==> ValidPtr(l', x); // true
  // assert forall x : AbInt {:trigger AbSeqIndex(x, l'.g)} :: ValidPtr(l, x) ==> AbSeqIndex(x, l'.g) == AbSeqIndex(x, l.g); // true

  Props_add_sub_is_orig ();
  // assert len == AbSub(AbAdd(len, I1), I1); // trigger
  Props_lt_subtraction ();
  // assert AbLeq(len, AbSub(len', I1));
  // Props_lt_transitive'_p3 (I0, len, AbSub(len', I1)); // 0 < len < len'-1
  // Props_lt_is_not_leq_p2 (I0, AbSub(len', I1));
  Props_lt_is_not_leq_px (AbAdd(len, I1));
  Props_lt_is_not_leq_py (AbAdd(len, I1));
  // assert l'.freeStack != I0; // true
  // assert AbSeqIndex(l'.freeStack, l'.nodes).data.None?; // true

  Props_lt_is_not_leq_px (len);
  Props_lt_is_not_leq_py (len);
  // Props_lt_transitive'_p3 (unused, sentinel, I0);
  // assert AbLt(unused, I0);
  // Props_lt_transitive'_p3 (unused, I0, AbSeqLen(s)); // unused < |s|

}

method InsertAfter<X>(l:DList<X>, p:AbInt, a:X) returns(l':DList<X>, p':AbInt)
  requires Inv(l)
  requires MaybePtr(l, p)
  ensures Inv(l')
  // ensures Seq(l') == Seq(l)[.. Index(l, p) + 1] + [a] + Seq(l)[Index(l, p) + 1 ..]
  ensures Seq(l') == AbSeqInsertIdx(AbAdd(Index(l, p), I1), a, Seq(l))
  ensures ValidPtr(l', p') && Index(l', p') == AbAdd(Index(l, p), I1)
  ensures forall x :: ValidPtr(l, x) ==>
    ValidPtr(l', x) &&
    if AbLeq(Index(l, x), Index(l, p)) then Index(l', x) == Index(l, x) else Index(l', x) == AbAdd(Index(l, x), I1)
{
  l' := l;
  p' := l'.freeStack;
  var freeNode := AbSeqIndex(p', l'.nodes);
  if (p' == I0 || freeNode.data.Some?) {
    l' := Expand(l');
    p' := l'.freeStack;
    freeNode := AbSeqIndex(p', l'.nodes);
  }
  var DList(nodes, freeStack, s, f, g) := l';
  ghost var index := AbSeqIndex(p, g);
  ghost var index' := AbAdd(index, I1);
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
