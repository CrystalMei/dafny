// include "ADT-int.dfy"
include "ADT-seq.dfy"

newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i < 0x1_0000_0000_0000_0000

// import opened ADT`Basic
import opened ADT`Basic
import opened ADT_Seq`Seq_Basic

datatype Option<V> = None | Some(value:V)
datatype Node<A> = Node(data:Option<A>, next:AbInt, prev:AbInt)
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
  // ensures Inv(l')
  ensures Seq(l') == AbSeqRemoveIdx(Index(l, p), Seq(l))
  // ensures forall x :: x != p && ValidPtr(l, x) ==>
  //   ValidPtr(l', x) &&
  //   ( if AbLt(Index(l, x), Index(l, p)) 
  //     then Index(l', x) == Index(l, x)
  //     else Index(l', x) == AbSub(Index(l, x), I1) )
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

    forall i | AbLeqLt(i, I0, AbSeqLen(f'))
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
    
    forall i | AbLeqLt(i, I0, AbSeqLen(f'))
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

///////////////////// short version ///////////////////////////
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
