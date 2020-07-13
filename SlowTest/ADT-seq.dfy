include "ADT-int.dfy"
module ADT_Seq {
  export Seq_Basic 
    provides
      AAI,
      AbSeq, 
      AbSeqLen, AbSeqIndex, AbSeqConcat, AbSeqIn, AbSeqEmpty, AbSeqSingleton, AbSeqSlice, /* AbSeqInit, */
      AbSeqGetIdx, AbSeqRemove, AbSeqRemoveIdx, AbSeqUpdate, AbSeqInsertIdx,

      Seq_Props_length_p1, Seq_Props_concat_length_p2,
      Seq_Props_concat_in_p3,
      Seq_Props_concat_in_part1_all_p3, Seq_Props_concat_in_part2_all_p3,
      Seq_Props_concat_in_all_part1_p3, Seq_Props_concat_in_all_part2_p3,
      Seq_Props_concat_index_part1_p3, Seq_Props_concat_index_part2_p3,
      Seq_Props_concat_is_orig_p2,
      Seq_Props_in_empty_p2, Seq_Props_in_non_empty_p2,
      Seq_Props_in_idx_p2, Seq_Props_idx_in_p2,
      Seq_Props_slice_in_p4

  import AI = ADT`Ultra
  import AAI = ADT`Basic

  type AbSeq<X(==)> = seq<X>
  function method AbSeqLen<X> (s: AbSeq<X>) : AI.AbInt { |s| }
  function method AbSeqIndex<X> (i: AI.AbInt, s: AbSeq<X>) : X
    requires AI.AbLeq(AI.I0, i)
    requires AI.AbLt(i, AbSeqLen(s))
    ensures AbSeqIn(AbSeqIndex(i, s), s)
    { s[i] }

  function method AbSeqConcat<X> (s1: AbSeq<X>, s2: AbSeq<X>) : AbSeq<X> { s1 + s2 }
  function method AbSeqIn<X> (v: X, s: AbSeq<X>) : bool { v in s }

  function method AbSeqEmpty<X> (): (s: AbSeq<X>)
    ensures AbSeqLen(s) == AI.I0 
    { [] }

  function method AbSeqSingleton<X(!new)> (v: X): (s: AbSeq<X>)
    ensures AbSeqLen(s) == AI.I1
    ensures AI.AbLt(AI.I0, AI.I1) ==> AbSeqIndex(AI.I0, s) == v
    ensures AbSeqIn(v, s)
    // ensures forall x :: x != v ==> !AbSeqIn(x, s)
    { [v] }

  function method AbSeqSlice<X> (i: AI.AbInt, j: AI.AbInt, s: AbSeq<X>) : (s' : AbSeq<X>)
    requires AI.AbLeq(AI.I0, i)
    requires AI.AbLeq(j, AbSeqLen(s))
    requires AI.AbLeq(i, j)
    ensures AbSeqLen(s') == AI.AbSub(j, i)
    ensures forall x : AI.AbInt
      // {:trigger AbSeqIndex(x, s)}
      {:trigger AbSeqIndex(AI.AbSub(x, i), s')} ::
      AI.AbLeqLt(x, i, j) ==> // i <= x < j
      // precond begins
      AI.AbLeq(AI.I0, x) ==> AI.AbLt(x, AbSeqLen(s)) ==>
      AI.AbLeq(AI.I0, AI.AbSub(x, i)) ==> AI.AbLt(AI.AbSub(x, i), AbSeqLen(s')) ==>
      // precond ends
      AbSeqIndex(x, s) == AbSeqIndex(AI.AbSub(x, i), s')
    { s[i..j] } // s[i..j] w/ s[i] and w/o s[j]

  function method AbSeqGetIdx<X>(v: X, s: AbSeq<X>) : (i: AI.AbInt)
    requires AbSeqIn(v, s)
    ensures AI.AbLeqLt(i, AI.I0, AbSeqLen(s))
    ensures AbSeqIndex(i, s) == v

  function method AbSeqRemove<X(!new)> (v: X, s: AbSeq<X>): (s': AbSeq<X>)
    requires AbSeqIn(v, s)
    ensures AbSeqLen(s) == AI.AbAdd(AbSeqLen(s'), AI.I1)
    ensures AbSeqLen(s') == AI.AbSub(AbSeqLen(s), AI.I1)
    // ensures forall x : X :: AbSeqIn(x, s') ==> AbSeqIn(x, s)
    ensures var k := AbSeqGetIdx(v, s);
      forall i : AI.AbInt // s[0, k) keeps
        {:trigger AbSeqIndex(i, s')} ::
        AI.AbLeqLt(i, AI.I0, k) ==>
        // precond begins
        AI.AbLt(i, AbSeqLen(s)) ==>
        AI.AbLt(i, AbSeqLen(s')) ==>
        // precond ends
        AbSeqIndex(i, s) == AbSeqIndex(i, s')
    ensures var k := AbSeqGetIdx(v, s);
      forall i : AI.AbInt // s[k, |s|-1) keeps
        {:trigger AbSeqIndex(AI.AbAdd(i, AI.I1), s)}
        {:trigger AbSeqIndex(i, s')} ::
        AI.AbLeqLt(i, k, AbSeqLen(s')) ==>
        // precond begins
        AI.AbLeq(AI.I0, i) ==>
        AI.AbLt(AI.I0, AI.AbAdd(i, AI.I1)) ==>
        AI.AbLt(AI.AbAdd(i, AI.I1), AbSeqLen(s)) ==>
        // precond ends
        AbSeqIndex(AI.AbAdd(i, AI.I1), s) == AbSeqIndex(i, s')

  function method AbSeqRemoveIdx<X(!new)> (k: AI.AbInt, s: AbSeq<X>) : (s': AbSeq<X>)
    requires AI.AbLeqLt(k, AI.I0, AbSeqLen(s))
    ensures AbSeqLen(s) == AI.AbAdd(AbSeqLen(s'), AI.I1)
    ensures AbSeqLen(s') == AI.AbSub(AbSeqLen(s), AI.I1)
    // ensures forall x: X :: AbSeqIn(x, s') ==> AbSeqIn(x, s)
    ensures
      forall i : AI.AbInt // s[0, k) keeps
        {:trigger AbSeqIndex(i, s')} ::
        AI.AbLeqLt(i, AI.I0, k) ==>
        // precond begins
        AI.AbLt(i, AbSeqLen(s)) ==>
        AI.AbLt(i, AbSeqLen(s')) ==>
        // precond ends
        AbSeqIndex(i, s) == AbSeqIndex(i, s')
    ensures
      forall i : AI.AbInt // s[k, |s|-1) keeps
        {:trigger AbSeqIndex(AI.AbAdd(i, AI.I1), s)}
        {:trigger AbSeqIndex(i, s')} ::
        AI.AbLeqLt(i, k, AbSeqLen(s')) ==>
        // precond begins
        AI.AbLeq(AI.I0, i) ==>
        AI.AbLt(AI.I0, AI.AbAdd(i, AI.I1)) ==>
        AI.AbLt(AI.AbAdd(i, AI.I1), AbSeqLen(s)) ==>
        // precond ends
        AbSeqIndex(AI.AbAdd(i, AI.I1), s) == AbSeqIndex(i, s')
    { s[ ..k ] + s[ k+1.. ] }

  function method AbSeqUpdate<X> (k: AI.AbInt, v: X, s: AbSeq<X>): (s': AbSeq<X>)
    requires AI.AbLeqLt(k, AI.I0, AbSeqLen(s))
    ensures AbSeqLen(s) == AbSeqLen(s')
    ensures AbSeqIndex(k, s') == v
    ensures
      forall i : AI.AbInt // s[0, k) keeps
        {:trigger AbSeqIndex(i, s')} ::
        AI.AbLeqLt(i, AI.I0, k) ==>
        // precond begins
        AI.AbLt(i, AbSeqLen(s)) ==>
        AI.AbLt(i, AbSeqLen(s')) ==>
        // precond ends
        AbSeqIndex(i, s) == AbSeqIndex(i, s')
    ensures
      forall i : AI.AbInt // s(k, |s|) keeps
        {:trigger AbSeqIndex(i, s')} ::
        AI.AbLt(k, i) && AI.AbLt(i, AbSeqLen(s')) ==>
        // precond begins
        AI.AbLeq(AI.I0, i) ==>
        AI.AbLt(i, AbSeqLen(s)) ==>
        // precond ends
        AbSeqIndex(i, s) == AbSeqIndex(i, s')
    { s[ k := v ] }

  function method AbSeqInsertIdx<X(!new)> (k: AI.AbInt, v: X, s: AbSeq<X>) : (s': AbSeq<X>)
    requires AI.AbLeq(AI.I0, k)
    requires AI.AbLeq(k, AbSeqLen(s))
    ensures AbSeqLen(s') == AI.AbAdd(AbSeqLen(s), AI.I1)
    ensures AbSeqIndex(k, s') == v
    ensures
      forall i : AI.AbInt // s[0, k) keeps
        {:trigger AbSeqIndex(i, s')} ::
        AI.AbLeqLt(i, AI.I0, k) ==>
        // precond begins
        AI.AbLt(i, AbSeqLen(s)) ==>
        AI.AbLt(i, AbSeqLen(s')) ==>
        // precond ends
        AbSeqIndex(i, s') == AbSeqIndex(i, s)
    ensures
      forall i : AI.AbInt // s[k, |s|) keeps
        {:trigger AbSeqIndex(AI.AbAdd(i, AI.I1), s')} ::
        AI.AbLeqLt(i, k, AbSeqLen(s)) ==>
        // precond begins
        AI.AbLeq(AI.I0, i) ==>
        AI.AbLt(AI.I0, AI.AbAdd(i, AI.I1)) ==>
        AI.AbLt(AI.AbAdd(i, AI.I1), AbSeqLen(s')) ==>
        // precond ends
        AbSeqIndex(i, s) == AbSeqIndex(AI.AbAdd(i, AI.I1), s')
  { s[..k] + [v] + s[k..] }

  lemma Seq_Props_length_p1<X> (s: AbSeq<X>) // |s| >= 0
    ensures AI.AbLeq(AI.I0, AbSeqLen(s))
    { }

  lemma Seq_Props_concat_length_p2<X> (s1: AbSeq<X>, s2: AbSeq<X>) // |s1 + s2| == |s1| + |s2|
    ensures AbSeqLen(AbSeqConcat(s1, s2)) == AI.AbAdd(AbSeqLen(s1), AbSeqLen(s2))
    { }
  
  lemma Seq_Props_concat_in_p3<X> (x: X, s1: AbSeq<X>, s2: AbSeq<X>) // x in s1 || x in s2 ==> x in s1 + s2
    requires AbSeqIn(x, s1) || AbSeqIn(x, s2)
    ensures AbSeqIn(x, AbSeqConcat(s1, s2))
    { }

  lemma Seq_Props_concat_in_part1_all_p3<X> (x: X, s1: AbSeq<X>, s2: AbSeq<X>)
    // x in s1 ==> x in s1 + s2
    requires AbSeqIn(x, s1)
    ensures AbSeqIn(x, AbSeqConcat(s1, s2))
  
  lemma Seq_Props_concat_in_part2_all_p3<X> (x: X, s1: AbSeq<X>, s2: AbSeq<X>)
    // x in s2 ==> x in s1 + s2
    requires AbSeqIn(x, s2)
    ensures AbSeqIn(x, AbSeqConcat(s1, s2))
    { }

  lemma Seq_Props_concat_in_all_part1_p3<X> (x: X, s1: AbSeq<X>, s2: AbSeq<X>)
    // x in s1 + s2 && x !in s2 ==> x in s1
    requires AbSeqIn(x, AbSeqConcat(s1, s2))
    requires !AbSeqIn(x, s2)
    ensures AbSeqIn(x, s1)
    { }

  lemma Seq_Props_concat_in_all_part2_p3<X> (x: X, s1: AbSeq<X>, s2: AbSeq<X>)
    // x in s1 + s2 && x !in s1 ==> x in s2
    requires AbSeqIn(x, AbSeqConcat(s1, s2))
    requires !AbSeqIn(x, s1)
    ensures AbSeqIn(x, s2)
    { }

  lemma Seq_Props_concat_index_part1_p3<X> (i: AI.AbInt, s1: AbSeq<X>, s2: AbSeq<X>)
    requires AI.AbLeqLt(i, AI.I0, AbSeqLen(s1)) // 0 <= i < |s1|
    requires AI.AbLt(i, AbSeqLen(AbSeqConcat(s1, s2))) // i < |s1| < |s1 + s2|
    ensures AbSeqIndex(i, s1) == AbSeqIndex(i, AbSeqConcat(s1, s2))
    { }

  lemma Seq_Props_concat_index_part2_p3<X> (i: AI.AbInt, s1: AbSeq<X>, s2: AbSeq<X>)
    requires AI.AbLeqLt(i, AI.I0, AbSeqLen(s2)) // 0 <= i < |s2|
    requires AI.AbLeq(AI.I0, AI.AbAdd(i, AbSeqLen(s1))) // 0 <= i + |s1|
    requires AI.AbLt(AI.AbAdd(i, AbSeqLen(s1)), AbSeqLen(AbSeqConcat(s1, s2)))  // i + |s1| < |s1 + s2|
    ensures AbSeqIndex(i, s2) == AbSeqIndex(AI.AbAdd(i, AbSeqLen(s1)), AbSeqConcat(s1, s2))
    { }

  lemma Seq_Props_concat_is_orig_p2<X> (i: AI.AbInt, s: AbSeq<X>)
    requires AI.AbLeqLt(i, AI.I0, AbSeqLen(s)) // 0 <= i < |s|
    ensures s == AbSeqConcat(AbSeqSlice(AI.I0, i, s), AbSeqSlice(i, AbSeqLen(s), s))
    { }

  lemma Seq_Props_in_empty_p2<X> (v: X, s: AbSeq<X>) // empty seq
    requires AbSeqLen(s) == AI.I0
    ensures !AbSeqIn(v, s)
    { }

  lemma Seq_Props_in_non_empty_p2<X> (v: X, s: AbSeq<X>) // i in s ==> |s| > 0
    requires AbSeqIn(v, s)
    ensures AI.AbLt(AI.I0, AbSeqLen(s))
    { }

  lemma Seq_Props_in_idx_p2<X> (v: X, s: AbSeq<X>) // v in s ==> s[i] == v
    requires AbSeqIn(v, s)
    ensures exists i: AI.AbInt :: AI.AbLeqLt(i, AI.I0, AbSeqLen(s)) && AbSeqIndex(i, s) == v
    { ghost var k :| 0 <= k < |s| && s[k] == v;
      // match the "exists" pattern
      assert AI.AbLeqLt(k, AI.I0, AbSeqLen(s)) && AbSeqIndex(k, s) == v; }
  
  lemma Seq_Props_idx_in_p2<X> (k: AI.AbInt, s: AbSeq<X>) // s[k] in s
    requires AI.AbLeqLt(k, AI.I0, AbSeqLen(s)) // 0 <= k < |s|
    ensures AbSeqIn(AbSeqIndex(k, s), s)
    { }
  
  lemma Seq_Props_slice_in_p4<X> (i: AI.AbInt, j: AI.AbInt, s: AbSeq<X>, v: X)
    requires AI.AbLeq(AI.I0, i) 
    requires AI.AbLeq(j, AbSeqLen(s))
    requires AI.AbLeq(i, j)
    ensures AbSeqIn(v, AbSeqSlice(i, j, s)) ==> AbSeqIn(v, s)
    { }
}

import opened ADT`Basic
import opened ADT_Seq`Seq_Basic

function method AbSeqInit<X> (len: AbInt, func : AbInt --> X) : (s: AbSeq<X>)
  requires AbLeq(I0, len)
  requires forall i : AbInt :: AbLeqLt(i, I0, len) ==> func.requires(i)
  ensures AbSeqLen(s) == len
  ensures forall i : AbInt
    {:trigger AbSeqIndex(i, s)} {: trigger func(i)} ::
    AbLeqLt(i, I0, len) ==> AbSeqIndex(i, s) == func(i)

function method AbSeqResize<X>(s: AbSeq<X>, newlen: AbInt, a: X) : (s': AbSeq<X>)
  ensures AbSeqLen(s') == newlen
  ensures forall j : AbInt
    {:trigger AbSeqIndex(j, s)}
    {:trigger AbSeqIndex(j, s')} ::
    AbLeqLt(j, I0, newlen) ==>
    AbSeqIndex(j, s') == (if AbLt(j, AbSeqLen(s)) then AbSeqIndex(j, s) else a) 

lemma Seq_Props_length<X> () // |s| >= 0
  ensures forall s: AbSeq<X> :: AbLeq(I0, AbSeqLen(s))
  { forall s { Seq_Props_length_p1<X> (s); } }

lemma Seq_Props_concat_length<X> () // |s1 + s2| == |s1| + |s2|
  ensures forall s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqLen(AbSeqConcat(s1, s2)) == AbAdd(AbSeqLen(s1), AbSeqLen(s2))
  { forall s1, s2 { Seq_Props_concat_length_p2<X>(s1, s2); } }

lemma Seq_Props_concat_in<X> () // x in s1 || x in s2 ==> x in s1 + s2
  ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, s1) || AbSeqIn(x, s2) ==> AbSeqIn(x, AbSeqConcat(s1, s2))
  { forall x, s1, s2 | AbSeqIn(x, s1) || AbSeqIn(x, s2)
    { Seq_Props_concat_in_p3<X>(x, s1, s2); } }

lemma Seq_Props_concat_in_part1_all<X> ()
  // x in s1 ==> x in s1 + s2
  ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, s1) ==> AbSeqIn(x, AbSeqConcat(s1, s2))
  { forall x, s1, s2 | AbSeqIn (x, s1) 
    { Seq_Props_concat_in_part1_all_p3<X>(x, s1, s2); } }

lemma Seq_Props_concat_in_part2_all<X> ()
  // x in s2 ==> x in s1 + s2
  ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, s2) ==> AbSeqIn(x, AbSeqConcat(s1, s2))
  { forall x, s1, s2 | AbSeqIn (x, s2) 
    { Seq_Props_concat_in_part2_all_p3<X>(x, s1, s2); } }

lemma Seq_Props_concat_in_all_part1<X> ()
  // x in s1 + s2 && x !in s2 ==> x in s1
  ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, AbSeqConcat(s1, s2)) && !AbSeqIn(x, s2) ==> AbSeqIn(x, s1)
  { forall x, s1, s2 | AbSeqIn(x, AbSeqConcat(s1, s2)) && !AbSeqIn(x, s2)
    { Seq_Props_concat_in_all_part1_p3<X>(x, s1, s2); } }

lemma Seq_Props_concat_in_all_part2<X> ()
  // x in s1 + s2 && x !in s1 ==> x in s2
  ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, AbSeqConcat(s1, s2)) && !AbSeqIn(x, s1) ==> AbSeqIn(x, s2)
  { forall x, s1, s2 | AbSeqIn(x, AbSeqConcat(s1, s2)) && !AbSeqIn(x, s1)
    { Seq_Props_concat_in_all_part2_p3<X>(x, s1, s2); } }

lemma Seq_Props_concat_index_part1<X> ()
  ensures forall i: AbInt, s1: AbSeq<X>, s2: AbSeq<X>
    {:trigger AbSeqIndex(i, AbSeqConcat(s1, s2))} ::
  AbLeqLt(i, I0, AbSeqLen(s1)) ==> // 0 <= i < |s1|
  AbLt(i, AbSeqLen(AbSeqConcat(s1, s2))) ==> // i < |s1| < |s1 + s2|
  AbSeqIndex(i, s1) == AbSeqIndex(i, AbSeqConcat(s1, s2))
  { forall i, s1, s2 | AbLeqLt(i, I0, AbSeqLen(s1)) && 
      AbLt(i, AbSeqLen(AbSeqConcat(s1, s2)))
    { Seq_Props_concat_index_part1_p3<X>(i, s1, s2); } }

lemma Seq_Props_concat_index_part2<X> ()
  ensures forall i: AbInt, s1: AbSeq<X>, s2: AbSeq<X>
    {:trigger AbSeqIndex(AbAdd(i, AbSeqLen(s1)), AbSeqConcat(s1, s2))} ::
    AbLeqLt(i, I0, AbSeqLen(s2)) ==>
    AbLeq(I0, AbAdd(i, AbSeqLen(s1))) ==> // 0 <= i + |s1|
    AbLt(AbAdd(i, AbSeqLen(s1)), AbSeqLen(AbSeqConcat(s1, s2))) ==> // i + |s1| < |s1 + s2|
    AbSeqIndex(i, s2) == AbSeqIndex(AbAdd(i, AbSeqLen(s1)), AbSeqConcat(s1, s2))
  { forall i, s1, s2 | AbLeqLt(i, I0, AbSeqLen(s2)) && 
      AbLeq(I0, AbAdd(i, AbSeqLen(s1))) && 
      AbLt(AbAdd(i, AbSeqLen(s1)), AbSeqLen(AbSeqConcat(s1, s2)))
    { Seq_Props_concat_index_part2_p3<X>(i, s1, s2); } }

lemma Seq_Props_concat_is_orig<X> ()
  ensures forall i: AbInt, s: AbSeq<X>
    {:trigger AbSeqSlice(I0, i, s)}
    {:trigger AbSeqSlice(i, AbSeqLen(s), s)} ::
    AbLeqLt(i, I0, AbSeqLen(s)) ==> // 0 <= i < |s|
    s == AbSeqConcat(AbSeqSlice(I0, i, s), AbSeqSlice(i, AbSeqLen(s), s))
  { forall i, s | AbLeqLt(i, I0, AbSeqLen(s))
    { Seq_Props_concat_is_orig_p2<X> (i, s); } }

lemma Seq_Props_in_empty<X> () // empty seq
  ensures forall v: X, s: AbSeq<X> :: AbSeqLen(s) == I0 ==> !AbSeqIn(v, s)
  {forall v, s | AbSeqLen(s) == I0
    { Seq_Props_in_empty_p2<X>(v, s); } }

lemma Seq_Props_in_non_empty<X> () // i in s ==> |s| > 0
  ensures forall v: X, s: AbSeq<X> :: AbSeqIn(v, s) ==> AbLt(I0, AbSeqLen(s))
  {forall v, s | AbSeqIn(v, s)
    { Seq_Props_in_non_empty_p2<X>(v, s); } }

lemma Seq_Props_in_idx<X> () // v in s ==> s[i] == v
  ensures forall v: X, s: AbSeq<X> :: AbSeqIn(v, s) ==>
    (exists i: AbInt :: AbLeqLt(i, I0, AbSeqLen(s)) && AbSeqIndex(i, s) == v )
  { forall v, s | AbSeqIn(v, s)
    { Seq_Props_in_idx_p2<X>(v, s); } }

lemma Seq_Props_idx_in<X> () // v in s ==> s[i] == v
  ensures forall k: AbInt, s: AbSeq<X>
    {:trigger AbSeqIndex(k, s)} ::
    AbLeqLt(k, I0, AbSeqLen(s)) ==>
    AbSeqIn(AbSeqIndex(k, s), s)
  { forall k, s | AbLeqLt(k, I0, AbSeqLen(s))
    {Seq_Props_idx_in_p2<X>(k, s); } }

lemma Seq_Props_slice_in<X> ()
  ensures forall i: AbInt, j: AbInt, s: AbSeq<X>, v: X
    {:trigger AbSeqIn(v, AbSeqSlice(i, j, s))} ::
    AbLeq(I0, i) && AbLeq(j, AbSeqLen(s)) && AbLeq(i, j) ==>
    AbSeqIn(v, AbSeqSlice(i, j, s)) ==> AbSeqIn(v, s)
  { forall i, j, s, v | AbLeq(I0, i) && AbLeq(j, AbSeqLen(s)) && AbLeq(i, j)
    { Seq_Props_slice_in_p4<X>(i, j, s, v); } }