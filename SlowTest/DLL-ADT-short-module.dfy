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
  && (forall i ::
    AbLeqLt(i, I0, AbSeqLen(f)) ==>
    AbLtLt(AbSeqIndex(i, f), I0, AbSeqLen(nodes)) )
  && (forall i {:trigger AbSeqIndex(AbSeqIndex(i, f), g)} ::
    AbLeqLt(i, I0, AbSeqLen(f)) ==>
    AbSeqIndex(AbSeqIndex(i, f), g) == i )
  && (forall p ::
    AbLeqLt(p, I0, AbSeqLen(g)) ==>
    && AbLeqLt(AbSeqIndex(p, g), unused, AbSeqLen(s))
    && AbLeqLt(AbSeqIndex(p, nodes).next, I0, AbSeqLen(g))
    && (AbLeq(I0, AbSeqIndex(p, g)) <==> AbSeqIndex(p, nodes).data.Some?) )
  && (forall p ::
    AbLeqLt(p, I0, AbSeqLen(g)) && AbLeq(sentinel, AbSeqIndex(p, g)) ==>
    && (AbSeqIndex(p, g) == sentinel ==> p == I0)
    && (AbLeq(I0, AbSeqIndex(p, g)) ==>
      AbSeqIndex(AbSeqIndex(p, g), f) == p &&
      AbSeqIndex(p, nodes).data == Some(AbSeqIndex(AbSeqIndex(p, g), s)))
    && (
      if AbLt(AbAdd(AbSeqIndex(p, g), I1), AbSeqLen(f)) then
        AbLt(I0, AbAdd(AbSeqIndex(p, g), I1)) ==> // precond: 0 < index
        AbSeqIndex(p, nodes).next == AbSeqIndex(AbAdd(AbSeqIndex(p, g), I1), f) // nonlast.next or sentinel.next
      else AbSeqIndex(p, nodes).next == I0 ) // last.next == sentinel or sentinel.next == sentinel
    && (
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
    )
}
predicate Inv<A>(l:DList<A>) { Invs(l.nodes, l.freeStack, l.s, l.f, l.g) }

function Seq<A>(l:DList<A>): AbSeq<A> { l.s }

function ValidPtr<A>(l:DList<A>, p:AbInt):(b:bool)
  ensures b ==> p != I0
  {
    // 0 < p < |l.g| && l.g[p] >= 0
    Props_lt_is_not_leq ();
    AbLtLt(p, I0, AbSeqLen(l.g)) &&
    AbLeq(I0, AbSeqIndex(p, l.g))
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
  ensures forall x :: x != p && ValidPtr(l, x) ==>
    ValidPtr(l', x) &&
    ( if AbLt(Index(l, x), Index(l, p)) 
      then Index(l', x) == Index(l, x)
      else Index(l', x) == AbSub(Index(l, x), I1) )
  {
    var DList(nodes, freeStack, s, f, g) := l;
    ghost var index := AbSeqIndex(p, g);
    // assert AbLeq(I0, index); // true
    // assert AbLt(index, AbSeqLen(f)); // true
    ghost var s' := AbSeqRemoveIdx(index, s); // s[.. index] + s[index + 1 ..];
    ghost var f' := AbSeqRemoveIdx(index, f); // f[.. index] + f[index + 1 ..];
    // // assert forall i :: AbLeqLt(i, I0, index) && 
    // //   AbLt(i, AbSeqLen(f)) && AbLt(i, AbSeqLen(f'))
    // //   ==> AbSeqIndex(i, f) == AbSeqIndex(i, f');    
    // forall i | AbLeqLt(i, I0, index) // s[0, k) keeps
    //   ensures AbSeqIndex(i, f) == AbSeqIndex(i, f')
    //   {
    //     Props_lt_transitive_p3(i, index, AbSeqLen(f));
    //     Props_lt2leq_sub (); // Props_lt2leq_sub_p2 (index, AbSeqLen(f));
    //     // assert AbLeq(index, AbSeqLen(f')); // true
    //     // Note: Leq -> cannot use precond-version transitive (which is Lt)
    //     Props_lt_transitive'_p3(i, index, AbSeqLen(f'));
    //   }
    // // assert forall i :: AbLt(index, i) && AbLt(i, AbSeqLen(f')) &&
    // //   AbLeq(I0, i) &&
    // //   AbLt(I0, AbAdd(i, I1)) && AbLt(AbAdd(i, I1), AbSeqLen(f))
    // //   ==> AbSeqIndex(AbAdd(i, I1), f) == AbSeqIndex(i, f');
    // forall i | AbLeqLt(i, index, AbSeqLen(f')) // s[k, |s|-1) keeps
    //   ensures AbSeqIndex(AbAdd(i, I1), f) == AbSeqIndex(i, f')
    //   {
    //     Props_lt_transitive'_p3(I0, index, i); // 0 <= index <= i
    //     Props_pos(I1);
    //     Props_add_pos_is_lt (); // Props_add_pos_is_lt_p2(i, I1); // i < i + 1
    //     Props_lt_transitive'_p3(I0, i, AbAdd(i, I1)); // 0 < i < i + 1
    //     // assert AbLt(I0, AbAdd(i, I1)); // 0 < i + 1
    //     Props_lt_addition_p3(i, AbSeqLen(f'), I1); // i + 1 < |f'| + 1 = |f|
    //     // assert AbLt(AbAdd(i, I1), AbSeqLen(f)); // i + 1 < |f|
    //   }
    Seq_Props_length<AbInt> (); // AbSeqLen(g/f) >= 0
    ghost var g' := AbSeqInit(AbSeqLen(g), // len >= 0
      x requires AbLeqLt(x, I0, AbSeqLen(g)) =>
      if AbSeqIndex(x, g) == index then unused
      else if AbLt(index, AbSeqIndex(x, g)) then AbSub(AbSeqIndex(x, g), I1)
      else AbSeqIndex(x, g) );
    // assert forall i :: AbLeqLt(i, I0, AbSeqLen(g)) ==>
    //   AbSeqIndex(i, g') == (if AbSeqIndex(i, g) == index then unused
    //   else if AbLt(index, AbSeqIndex(i, g)) then AbSub(AbSeqIndex(i, g), I1)
    //   else AbSeqIndex(i, g));
    var node := AbSeqIndex(p, nodes);
    /*** precond for AbSeqIndex(node.prev, nodes) */
    Props_leq2lt_sub_p2 (I0, index);
    // assert AbLeq(sentinel, index); // true
    Props_lt_is_not_leq (); // Props_lt_is_not_leq_p2 (I0, index);
    Props_lt2leq_sub ();
    // assert AbLt(I0, index) ==> AbLeq(I0, AbSub(index, I1)); // true
    // assert AbLt(index, AbSeqLen(f)); // true
    Props_pos(I1);
    Props_add_sub_is_orig_p2 (index, I1);
    Props_lt_add_notneg (); // Props_lt_add_notneg_p3 (AbSub(index, I1), AbSeqLen(f), I1);
    // assert AbLt(AbSub(index, I1), AbSeqLen(f)); // true
    // assert
    //   if AbLt(I0, index) then
    //     AbLeq(I0, AbSub(index, I1)) ==> // precond: 0 <= index
    //     AbLt(AbSub(index, I1), AbSeqLen(f)) ==> // precond: index < |f|
    //     AbSeqIndex(p, nodes).prev == AbSeqIndex(AbSub(index, I1), f) // nonfirst.prev
    //   else if I0 == index || I0 == AbSeqLen(f) then
    //     AbSeqIndex(p, nodes).prev == I0 // first.prev == sentinel or sentinel.prev == sentinel
    //   else
    //     AbLeq(I0, AbSub(AbSeqLen(f), I1)) ==> // precond: 0 <= index
    //     AbLt(AbSub(AbSeqLen(f), I1), AbSeqLen(f)) ==> // precond: index < |f|
    //     AbSeqIndex(p, nodes).prev == AbSeqIndex(AbSub(AbSeqLen(f), I1), f) ; // sentinel.prev == last
    // assert AbLeq(I0, node.prev); // true
    // assert AbLt(node.prev, AbSeqLen(nodes)); // true
    /*** precond ends */
    var node_prev := AbSeqIndex(node.prev, nodes);
    var nodes' := AbSeqUpdate(node.prev, node_prev.(next := node.next), nodes);
    var node_next := AbSeqIndex(node.next, nodes);
    var nodes'' := AbSeqUpdate(node.next, node_next.(prev := node.prev), nodes');
    var nodes''' := AbSeqUpdate(p, Node(None, freeStack, I0), nodes'');
    l' := DList(nodes''', p, s', f', g');
    
    // assert forall x :: x != p && ValidPtr(l, x) ==> ValidPtr(l', x); // true
    // assert forall x :: x != p && ValidPtr(l, x) ==>
    //   ( if AbLt(Index(l, x), Index(l, p)) 
    //     then Index(l', x) == Index(l, x)
    //     else Index(l', x) == AbSub(Index(l, x), I1) );

    /* check Inv(l') */
    Props_add_pos_is_lt ();
    assert AbSeqLen(f') == AbSeqLen(s'); // true
    assert AbSeqLen(g') == AbSeqLen(nodes); // true
    assert AbLt(I0, AbSeqLen(nodes)); // true
    assert AbLeq(I0, index); // true
    assert AbSeqIndex(I0, g') == sentinel; // true
    assert AbLeqLt(p, I0, AbSeqLen(nodes)); // true

    AbSeqRemoveIdx_Part1Same (index, s, s');
    AbSeqRemoveIdx_Part2Shift1 (index, s, s');
    AbSeqRemoveIdx_Part1Same (index, f, f');
    AbSeqRemoveIdx_Part2Shift1 (index, f, f');

    AbSeqRemoveIdx_InSame (f, f');

    forall i {:trigger AbSeqIndex(i, f')} | AbLeqLt(i, I0, AbSeqLen(f'))
      ensures
        if AbLeqLt(i, I0, index) then AbSeqIndex(i, f') == AbSeqIndex(i, f)
        else AbSeqIndex(i, f') == AbSeqIndex(AbAdd(i, I1), f)
      { 
        Props_lt_transitive'_p3(i, index, AbSeqLen(f));
        Props_lt2leq_sub (); // Props_lt2leq_sub_p2 (index, AbSeqLen(f));
        // assert AbLeq(index, AbSeqLen(f')); // true
        // Note: Leq -> cannot use precond-version transitive (which is Lt)
        Props_lt_transitive'_p3(i, index, AbSeqLen(f'));

        Props_lt_transitive'_p3(I0, index, i); // 0 <= index <= i
        Props_pos(I1);
        Props_add_pos_is_lt (); // Props_add_pos_is_lt_p2(i, I1); // i < i + 1
        Props_lt_transitive'_p3(I0, i, AbAdd(i, I1)); // 0 < i < i + 1
        // assert AbLt(I0, AbAdd(i, I1)); // 0 < i + 1
        Props_lt_addition_p3(i, AbSeqLen(f'), I1); // i + 1 < |f'| + 1 = |f|
        // assert AbLt(AbAdd(i, I1), AbSeqLen(f)); // i + 1 < |f|
      }
    
    forall i {:trigger AbSeqIndex(i, f')} | AbLeqLt(i, I0, AbSeqLen(f'))
      ensures AbLeqLt(AbAdd(i, I1), I0, AbSeqLen(f))
    {
      Props_pos(I1);
      // Props_add_pos_is_lt_p2(i, I1); // i < i + 1
      Props_add_pos_is_lt (); 
      // assert AbLt(i, AbAdd(i, I1));
      Props_lt_transitive'_p3(I0, i, AbAdd(i, I1)); // 0 < i < i + 1
      // assert AbLt(I0, AbAdd(i, I1)); // 0 < i + 1
      Props_lt_addition_p3(i, AbSeqLen(f'), I1); // i + 1 < |f'| + 1 = |f|
      // assert AbLt(AbAdd(i, I1), AbSeqLen(f)); // i + 1 < |f|
    }

    AbSeqUpdate_Part1Same (node.prev, node_prev.(next := node.next), nodes, nodes');
    AbSeqUpdate_Part2Same (node.prev, node_prev.(next := node.next), nodes, nodes');
    AbSeqUpdate_Part1Same (node.next, node_next.(prev := node.prev), nodes', nodes'');
    AbSeqUpdate_Part2Same (node.next, node_next.(prev := node.prev), nodes', nodes'');
    AbSeqUpdate_Part1Same (p, Node(None, freeStack, I0), nodes'', nodes''');
    AbSeqUpdate_Part2Same (p, Node(None, freeStack, I0), nodes'', nodes''');

    Seq_Props_all_p2 (f, f');
    // Seq_Props_index_props ();

    // assert forall i ::
    //   AbLeqLt(i, I0, AbSeqLen(f')) ==>
    //   AbLt(I0, AbSeqIndex(i, f'));
    // assert forall i ::
    //   AbLeqLt(i, I0, AbSeqLen(f')) ==>
    //   AbLt(AbSeqIndex(i, f'), AbSeqLen(nodes));

    // assert (forall i {:trigger AbSeqIndex(AbSeqIndex(i, f'), g')} ::
    //   AbLeqLt(i, I0, AbSeqLen(f')) ==>
    //   AbSeqIndex(AbSeqIndex(i, f'), g') == i );

    // assert (forall i ::
    //   AbLeqLt(i, I0, AbSeqLen(g')) ==>
    //   && AbLeqLt(AbSeqIndex(i, g'), unused, AbSeqLen(s'))
    //   && AbLeqLt(AbSeqIndex(i, nodes).next, I0, AbSeqLen(g'))
    //   && (AbLeq(I0, AbSeqIndex(i, g')) <==> AbSeqIndex(i, nodes).data.Some?) );
    // assert (forall p ::
    //   ((AbLt(I0, p) || I0 == p) && AbLt(p, AbSeqLen(g'))) &&
    //   (AbLt(sentinel, AbSeqIndex(p, g')) || sentinel == AbSeqIndex(p, g')) ==>
    //   && (AbSeqIndex(p, g') == sentinel ==> p == I0)
    //   && ((AbLt(I0, AbSeqIndex(p, g')) || I0 == AbSeqIndex(p, g')) ==>
    //       AbSeqIndex(AbSeqIndex(p, g'), f') == p && AbSeqIndex(p, nodes).data == Some(AbSeqIndex(AbSeqIndex(p, g'), s')))
    //   && (if AbLt(AbAdd(AbSeqIndex(p, g'), I1), AbSeqLen(f')) then
    //       AbLt(I0, AbAdd(AbSeqIndex(p, g'), I1)) ==> // precond: 0 < index
    //       AbSeqIndex(p, nodes).next == AbSeqIndex(AbAdd(AbSeqIndex(p, g'), I1), f') // nonlast.next or sentinel.next
    //     else AbSeqIndex(p, nodes).next == I0 ) // last.next == sentinel or sentinel.next == sentinel
    //   && (if AbLt(I0, AbSeqIndex(p, g')) then
    //       AbLt(I0, AbSub(AbSeqIndex(p, g'), I1)) || I0 == AbSub(AbSeqIndex(p, g'), I1) ==> // precond: 0 <= index
    //       AbLt(AbSub(AbSeqIndex(p, g'), I1), AbSeqLen(f')) ==> // precond: index < |f|
    //       AbSeqIndex(p, nodes).prev == AbSeqIndex(AbSub(AbSeqIndex(p, g'), I1), f') // nonfirst.prev
    //     else if I0 == AbSeqIndex(p, g') || I0 == AbSeqLen(f') then AbSeqIndex(p, nodes).prev == I0 // first.prev == sentinel or sentinel.prev == sentinel
    //     else
    //       AbLt(I0, AbSub(AbSeqLen(f'), I1)) || I0 == AbSub(AbSeqLen(f'), I1) ==> // precond: 0 <= index
    //       AbLt(AbSub(AbSeqLen(f'), I1), AbSeqLen(f')) ==> // precond: index < |f|
    //       AbSeqIndex(p, nodes).prev == AbSeqIndex(AbSub(AbSeqLen(f'), I1), f') ) // sentinel.prev == last
    //   );

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
    Props_lt2leq_add_p2 (n, AbSeqLen(b'));

    /** AbLeqLt(i, I0, k) ==> AbSeqIndex(i, b) == AbSeqIndex(i, a) */
    forall i : AbInt | AbLt(i, k) ensures AbLt(i, AbSeqLen(a)) { }

    /** AbLeqLt(i, k, n) ==> AbSeqIndex(i, b) == Node(None, AbSub(i, I1), I0) */
    forall i | AbLeqLt(i, k, n) ensures AbLt(I0, i) && AbLt(i, AbSeqLen(b')) { }
    forall i | AbLeqLt(i, k, AbAdd(n, I1)) ensures AbLt(I0, i) && AbLt(i, AbSeqLen(b')) { }
    forall i | AbLt(i, AbAdd(n, I1)) ensures AbLeq(i, n)
      { Props_lt2leq_sub_p2 (i, AbAdd(n, I1));
        Props_add_sub_is_orig_p2 (n, I1); }

    // decreases
    Props_sub_add_is_sub(); // x - (y + 1) == x - y - 1
    Props_pos(I1); // 1 > 0
    Props_add_pos_is_lt (); // x < x + 1
    Props_add_sub_is_orig (); // (x - 1) + 1 == x
    Props_adt_dt_lt (AbSub(AbSeqLen(b'), AbAdd(n, I1)), AbSub(AbSeqLen(b'), n));

    n := AbAdd(n, I1);
    b := b';
  }
}

method Expand<X> (l:DList<X>) returns (l':DList<X>)
  requires Inv(l)
  // ensures Inv(l') // error
  ensures l'.s == l.s
  // ensures forall x :: ValidPtr(l, x) ==> 
  //   ValidPtr(l', x) && 
  //   AbSeqIndex(x, l'.g) == AbSeqIndex(x, l.g)
  // ensures l'.freeStack != I0 && AbSeqIndex(l'.freeStack, l'.nodes).data.None?
{
  var DList(nodes, freeStack, s, f, g) := l;
  var len := AbSeqLen(nodes); // len > 0
  var len' := AbAdd(len, len);
  var nodes_orig := nodes;
  nodes := AbSeqResize(nodes, len', Node(None, freeStack, I0));

  Props_pos(I1);
  Props_add_pos_is_lt(); // len < len + 1, len < len'
  Props_lt_transitive_p3(I0, len, AbAdd(len, I1)); // 0 < len < len + 1
  Props_lt2leq_add_p2(I0, len);
  Props_add_identity (); // 1 <= len
  Props_add_commutative ();
  Props_lt_addition (); // len + 1 <= len + len = len'
  nodes := BuildFreeStack(nodes, AbAdd(len, I1));

  Seq_Props_length<Node<X>> ();
  ghost var g' := AbSeqInit( AbSeqLen(nodes),
    i requires AbLeqLt(i, I0, AbSeqLen(nodes)) =>
      if AbLt(i, AbSeqLen(g)) then AbSeqIndex(i, g) else unused );
  Props_lt_transitive_pyz (len, len'); // |g| < |g'|
  // assert forall p : AbInt :: AbLeqLt(p, I0, len) ==> AbSeqIndex(p, g') == AbSeqIndex(p, g);
  l' := DList(nodes, AbSub(len', I1), s, f, g');

  // assert forall x :: ValidPtr(l, x) ==> ValidPtr(l', x); // true
  // assert forall x :: ValidPtr(l, x) ==> AbSeqIndex(x, l'.g) == AbSeqIndex(x, l.g); // true
  Props_lt_transitive'_p3 (I1, AbAdd(len, I1), len');
  // assert AbLt(I1, AbAdd(len, I1));
  Props_lt_subtraction (); // I1 < len' ==> I0 < len' - 1
  Props_add_sub_is_orig_p2 (I0, I1);
  Props_add_sub_is_orig_p2(len, I1);
  Props_add_sub_is_orig_p2(len', I1);
  Props_lt_is_not_leq ();
  // assert l'.freeStack != I0; // true
  // assert AbSeqIndex(l'.freeStack, l'.nodes).data.None?; // true

  Seq_Props_length<X> ();
  Props_add_sub_is_orig_p2 (AbSub(I0, I1), I1);
  // Props_lt_transitive (); // XXX: use this, won't finish soon
  Props_lt_transitive_p3 (unused, sentinel, I0);
  Props_lt_transitive'_p3 (unused, I0, AbSeqLen(s));
  // assert forall p :: AbLeqLt(p, I0, AbSeqLen(g')) ==>
  //   AbLeqLt(AbSeqIndex(p, g'), unused, AbSeqLen(s));
  
  // Props_lt_transitive_p3(freeStack, len, len');
  // forall i | AbLeqLt(i, AbAdd(len, I1), len')
  //   ensures AbLeqLt(AbSub(i, I1), I0, len')
  //   { 
  //     Props_lt_transitive'_p3 (I0, len, AbSub(i, I1));
  //     Props_lt_transitive_p3 (AbSub(i, I1), AbSub(len', I1), len');
  //   }
  // // assert forall p :: AbLeqLt(p, I0, AbSeqLen(g')) ==>
  // //   AbLeqLt(AbSeqIndex(p, nodes).next, I0, AbSeqLen(g'));

  // assert AbLt(unused, I0);
  assert forall p {:trigger AbSeqIndex(p, g)} :: AbLeqLt(p, I0, AbSeqLen(g)) ==> (AbLeq(I0, AbSeqIndex(p, g)) ==> AbSeqIndex(p, nodes_orig).data.Some?);
  assert forall p {:trigger AbSeqIndex(p, g')} :: AbLeqLt(p, I0, AbSeqLen(g)) ==> (AbLeq(I0, AbSeqIndex(p, g')) ==> AbLeq(I0, AbSeqIndex(p, g)));
  // assert false;
  // assert forall p :: AbLeqLt(p, I0, AbSeqLen(g)) ==>
  //   (AbLeq(I0, AbSeqIndex(p, g')) ==> AbSeqIndex(p, nodes_orig).data.Some?);
  // assume forall p :: AbLeqLt(p, I0, AbSeqLen(g')) ==>
  //   (AbLeq(I0, AbSeqIndex(p, g')) ==> AbLeqLt(p, I0, AbSeqLen(g)));
  // assert forall p :: AbLeqLt(p, I0, AbSeqLen(g)) ==>
  //   (AbLeq(I0, AbSeqIndex(p, g')) ==> AbSeqIndex(p, nodes).data.Some?);
  // assert forall p :: AbLeqLt(p, I0, AbSeqLen(g')) ==>
  //   (AbLeq(I0, AbSeqIndex(p, g')) ==> AbSeqIndex(p, nodes).data.Some?);
  // assert false;
  
  // assert forall p :: AbLeqLt(p, I0, AbSeqLen(g')) ==>
  //   (AbSeqIndex(p, nodes).data.Some? ==> AbLeq(I0, AbSeqIndex(p, g')));
  // assert Inv(l');
}

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
