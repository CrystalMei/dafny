include "ADT-int.dfy"
module ADT_Seq refines ADT {
  export Basic 
    provides AbSeq,
      AbSeqLen, AbSeqIndex, AbSeqConcat, AbSeqIn, AbSeqEmpty, AbSeqSingleton, AbSeqSlice,
      AbSeqGetIdx, AbSeqRemove, AbSeqRemoveIdx, AbSeqUpdate, AbSeqInit,

      Seq_Props_length_p1, Seq_Props_concat_length_p2,
      Seq_Props_concat_in_p3, Seq_Props_concat_in_part2all_p3, Seq_Props_concat_in_all2part_p3,
      Seq_Props_concat_index_part1_p3, Seq_Props_concat_index_part2_p3,
      Seq_Props_concat_is_orig_p2,
      Seq_Props_in_empty_p2, Seq_Props_in_non_empty_p2,
      Seq_Props_in_idx_p2,
      Seq_Props_slice_in_p4

  import opened ADT_Int
  type AbSeq<X(==)> = seq<X>
  function method AbSeqLen<X> (s: AbSeq<X>) : AbInt { |s| }
  function method AbSeqIndex<X> (i: AbInt, s: AbSeq<X>) : X
    requires AbLeq(I0, i)
    requires AbLt(i, AbSeqLen(s))
    ensures AbSeqIn(AbSeqIndex(i, s), s)
    { s[i] }

  function method AbSeqConcat<X> (s1: AbSeq<X>, s2: AbSeq<X>) : AbSeq<X> { s1 + s2 }
  function method AbSeqIn<X> (v: X, s: AbSeq<X>) : bool { v in s }

  function method AbSeqEmpty<X> (): (s: AbSeq<X>)
    ensures AbSeqLen(s) == I0
    { [] }

  function method AbSeqSingleton<X(!new)> (v: X): (s: AbSeq<X>)
    ensures AbSeqLen(s) == I1
    ensures AbLt(I0, I1) ==> AbSeqIndex(I0, s) == v
    ensures AbSeqIn(v, s)
    ensures forall x :: x != v ==> !AbSeqIn(x, s)
    { [v] }

  function method AbSeqSlice<X> (i: AbInt, j: AbInt, s: AbSeq<X>) : (s' : AbSeq<X>)
    requires AbLeq(I0, i)
    requires AbLeq(j, AbSeqLen(s))
    requires AbLeq(i, j)
    ensures AbSeqLen(s') == AbSub(j, i)
    ensures forall x :: AbLeq(i, x) && AbLt(x, j) ==>
      // precond begins
      AbLeq(I0, x) ==> AbLt(x, AbSeqLen(s)) ==>
      AbLeq(I0, AbSub(x, i)) ==> AbLt(AbSub(x, i), AbSeqLen(s')) ==>
      // precond ends
      AbSeqIndex(x, s) == AbSeqIndex(AbSub(x, i), s') // s[i..j] w/ s[i] and w/o s[j]
    { s[i..j] }

  function method AbSeqGetIdx<X>(v: X, s: AbSeq<X>) : (i: AbInt)
    requires AbSeqIn(v, s)
    ensures AbLeqLt(i, I0, AbSeqLen(s))
    ensures AbSeqIndex(i, s) == v

  function method AbSeqInit<X> (len: AbInt, func : AbInt --> X) : (s: AbSeq<X>)
    requires forall i :: AbLeq(I0, i) && AbLt(i, len) ==> func.requires(i)
    ensures AbSeqLen(s) == len
    ensures forall i :: AbLeqLt(i, I0, len) ==>
      AbSeqIndex(i, s) == func(i)

  function method AbSeqRemove<X(!new)> (v: X, s: AbSeq<X>): (s': AbSeq<X>)
    requires AbSeqIn(v, s)
    ensures AbSeqLen(s) == AbAdd(AbSeqLen(s'), I1)
    ensures AbSeqLen(s') == AbSub(AbSeqLen(s), I1)
    ensures forall v :: AbSeqIn(v, s') ==> AbSeqIn(v, s)
    ensures var k := AbSeqGetIdx(v, s);
      forall i :: // s[0, k) keeps
        AbLeqLt(i, I0, k) ==>
        // precond begins
        AbLt(i, AbSeqLen(s)) ==>
        AbLt(i, AbSeqLen(s')) ==>
        // precond ends
        AbSeqIndex(i, s) == AbSeqIndex(i, s')
    ensures var k := AbSeqGetIdx(v, s);
      forall i :: // s(k, |s|-1] keeps
        AbLt(k, i) && AbLt(i, AbSeqLen(s')) ==>
        // precond begins
        AbLeq(I0, i) ==>
        AbLt(I0, AbAdd(i, I1)) ==>
        AbLt(AbAdd(i, I1), AbSeqLen(s)) ==>
        // precond ends
        AbSeqIndex(AbAdd(i, I1), s) == AbSeqIndex(i, s')
  {
    var k := AbSeqGetIdx(v, s);
    AbSeqRemoveIdx(k, s)
  }

  function method AbSeqRemoveIdx<X(!new)> (k: AbInt, s: AbSeq<X>) : (s': AbSeq<X>)
    requires AbLt(k, AbSeqLen(s))
    requires AbLt(I0, k) || I0 == k
    ensures AbSeqLen(s) == AbAdd(AbSeqLen(s'), I1)
    ensures AbSeqLen(s') == AbSub(AbSeqLen(s), I1)
    ensures forall v :: AbSeqIn(v, s') ==> AbSeqIn(v, s)
    ensures
      forall i :: // s[0, k) keeps
        AbLeqLt(i, I0, k) ==>
        // precond begins
        AbLt(i, AbSeqLen(s)) ==>
        AbLt(i, AbSeqLen(s')) ==>
        // precond ends
        AbSeqIndex(i, s) == AbSeqIndex(i, s')
    ensures
      forall i :: // s(k, |s|-1] keeps
        AbLt(k, i) && AbLt(i, AbSeqLen(s')) ==>
        // precond begins
        AbLeq(I0, i) ==>
        AbLt(I0, AbAdd(i, I1)) ==>
        AbLt(AbAdd(i, I1), AbSeqLen(s)) ==>
        // precond ends
        AbSeqIndex(AbAdd(i, I1), s) == AbSeqIndex(i, s')
  {
    var len := AbSeqLen(s);
    var half1 := AbSeqSlice(I0, k, s);
    Props_add2sub ();
    Props_add_identity ();
    Props_notneg ();
    assume AbPos(I1); // Props_pos (I1);
    Props_add_pos_is_lt ();
    Props_lt_transitive ();
    if AbLt(AbAdd(k, I1), len) then
      var half2 := AbSeqSlice(AbAdd(k, I1), len, s);
      // var s':= AbSeqConcat(half1, half2);
      Seq_Props_concat_length_p2 (half1, half2);
      Props_add_associative ();
      Props_lt_addition ();
      Seq_Props_concat_index_part1<X> ();
      // assert forall i :: // s[0, k) keeps
      //   (AbLt(I0, i) || I0 == i) &&
      //   AbLt(i, k) ==> 
      //   AbSeqIndex(i, s) == AbSeqIndex(i, s');
      Props_add_commutative ();
      Seq_Props_concat_index_part2<X> ();
      // assert forall i :: // s(k, |s|-1] keeps
      //   (AbLt(k, i) || i == k) &&
      //   AbLt(i, AbSeqLen(s')) ==>
      //   AbSeqIndex(AbAdd(i, I1), s) == 
      //   AbSeqIndex(i, s');
      Seq_Props_slice_in<X> ();
      Seq_Props_concat_in<X> ();
      // assert forall v :: AbSeqIn(v, s') ==> AbSeqIn(v, s);
      AbSeqConcat(half1, half2)
    else
      Props_lt_is_not_leq ();
      Props_lt2leq ();
      Seq_Props_slice_in<X> ();
      // assert forall v :: AbSeqIn(v, half1) ==> AbSeqIn(v, s);
      // assert forall i :: // s[0, k) keeps
      //   (AbLt(I0, i) || I0 == i) &&
      //   AbLt(i, AbSub(len, I1)) ==> 
      //   AbSeqIndex(i, s) == AbSeqIndex(i, s');
      // assert forall i :: // s(k, |s|-1] keeps
      //   (AbLt(k, i) || i == k) &&
      //   AbLt(i, AbSeqLen(s')) ==>
      //   AbSeqIndex(AbAdd(i, I1), s) == AbSeqIndex(i, s');
      half1
  }

  function method AbSeqUpdate<X> (k: AbInt, v: X, s: AbSeq<X>): (s': AbSeq<X>)
    requires AbLt(k, AbSeqLen(s))
    requires AbLeq(I0, k)
    ensures AbSeqLen(s) == AbSeqLen(s')
    ensures AbSeqIndex(k, s') == v
    ensures
      forall i :: // s[0, k) keeps
        AbLeqLt(i, I0, k) ==>
        // precond begins
        AbLt(i, AbSeqLen(s)) ==>
        AbLt(i, AbSeqLen(s')) ==>
        // precond ends
        AbSeqIndex(i, s) == AbSeqIndex(i, s')
    ensures
      forall i :: // s(k, |s|-1] keeps
        AbLt(k, i) && AbLt(i, AbSeqLen(s')) ==>
        // precond begins
        AbLeq(I0, i) ==>
        AbLt(i, AbSeqLen(s)) ==>
        // precond ends
        AbSeqIndex(i, s) == AbSeqIndex(i, s')
  {
    var len := AbSeqLen(s);
    var half1 := AbSeqSlice(I0, k, s);
    Props_add2sub ();
    Props_add_identity ();
    Props_notneg ();
    assume AbPos(I1); // Props_pos (I1);
    Props_add_pos_is_lt ();
    Props_lt_transitive ();
    Props_add_commutative ();
    if AbLt(AbAdd(k, I1), len) then
      var half2 := AbSeqSlice(AbAdd(k, I1), len, s);
      var half1' := AbSeqConcat(half1, AbSeqSingleton(v));
      Seq_Props_concat_length_p2 (half1, AbSeqSingleton(v));
      Seq_Props_concat_length_p2 (half1', half2);
      // var s' := AbSeqConcat(half1', half2);
      // assert len == AbSeqLen(s');
      Props_lt_addition ();
      Seq_Props_concat_index_part1<X> ();
      // assert forall i :: // s[0, k) keeps
      //   (AbLt(I0, i) || I0 == i) &&
      //   AbLt(i, k) ==>
      //   AbSeqIndex(i, s) == AbSeqIndex(i, s');
      // Seq_Props_concat_is_orig<X> ();
      Seq_Props_concat_is_orig_p2 (AbAdd(k, I1), s);
      Seq_Props_concat_index_part2<X> ();
      // Seq_Props_concat_index_part2_param (I0, half1, AbSeqSingleton(v));
      // assert AbSeqIndex(k, half1') == v;
      
      // assert forall i :: // s(k, |s|-1] keeps
      //   AbLt(k, i) && AbLt(i, AbSeqLen(s)) ==>
      //   AbSeqIndex(i, s) == AbSeqIndex(AbSub(i, AbAdd(k, I1)), half2);
      // assert forall i :: // s(k, |s|-1] keeps
      //   AbLt(k, i) &&
      //   AbLt(i, AbSeqLen(s')) ==>
      //   AbSeqIndex(i, s) == AbSeqIndex(i, s');
      AbSeqConcat(half1', half2)
    else
      Props_lt_is_not_leq_p2 (AbAdd(k, I1), len);
      Props_lt2leq ();
      // var s' := AbSeqConcat(half1, AbSeqSingleton(v));
      Seq_Props_concat_length_p2 (half1, AbSeqSingleton(v));
      // assert AbSeqLen(s') == len;
      Seq_Props_concat_index_part1<X> ();
      // assert forall i :: // s[0, k) keeps
      //   (AbLt(I0, i) || I0 == i) &&
      //   AbLt(i, k) ==>
      //   AbSeqIndex(i, s) == AbSeqIndex(i, s');
      // assert forall i :: // s(k, |s|-1] keeps
      //   AbLt(k, i) &&
      //   AbLt(i, AbSeqLen(s')) ==>
      //   AbSeqIndex(i, s) == AbSeqIndex(i, s');
      Seq_Props_concat_index_part2<X> ();
      // assert AbSeqIndex(k, s') == v;
      AbSeqConcat(half1, AbSeqSingleton(v))
}

  lemma Seq_Props_length_p1<X> (s: AbSeq<X>) // |s| >= 0
    ensures forall s: AbSeq<X> :: AbLeq(I0, AbSeqLen(s))
    {}
  lemma Seq_Props_length<X> () // |s| >= 0
    ensures forall s: AbSeq<X> :: AbLeq(I0, AbSeqLen(s))
    { forall s { Seq_Props_length_p1<X> (s); } }

  lemma Seq_Props_concat_length_p2<X> (s1: AbSeq<X>, s2: AbSeq<X>) // |s1 + s2| == |s1| + |s2|
    ensures AbSeqLen(AbSeqConcat(s1, s2)) == AbAdd(AbSeqLen(s1), AbSeqLen(s2))
    { }
  lemma Seq_Props_concat_length<X> () // |s1 + s2| == |s1| + |s2|
    ensures forall s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqLen(AbSeqConcat(s1, s2)) == AbAdd(AbSeqLen(s1), AbSeqLen(s2))
    { forall s1, s2 { Seq_Props_concat_length_p2<X>(s1, s2); } }
  
  lemma Seq_Props_concat_in_p3<X> (x: X, s1: AbSeq<X>, s2: AbSeq<X>) // x in s1 || x in s2 <==> x in s1 + s2
    ensures AbSeqIn(x, s1) || AbSeqIn(x, s2) <==> AbSeqIn(x, AbSeqConcat(s1, s2))
    { }
  lemma Seq_Props_concat_in<X> () // x in s1 || x in s2 <==> x in s1 + s2
    ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, s1) || AbSeqIn(x, s2) <==> AbSeqIn(x, AbSeqConcat(s1, s2))
    { forall x, s1, s2 { Seq_Props_concat_in_p3<X>(x, s1, s2); } }

  lemma Seq_Props_concat_in_part2all_p3<X> (x: X, s1: AbSeq<X>, s2: AbSeq<X>)
    // x in s1 ==> x in s1 + s2
    ensures AbSeqIn(x, s1) ==> AbSeqIn(x, AbSeqConcat(s1, s2))
    // x in s2 ==> x in s1 + s2
    ensures AbSeqIn(x, s2) ==> AbSeqIn(x, AbSeqConcat(s1, s2))
    { }
  lemma Seq_Props_concat_in_part2all<X> ()
    // x in s1 ==> x in s1 + s2
    ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, s1) ==> AbSeqIn(x, AbSeqConcat(s1, s2))
    // x in s2 ==> x in s1 + s2
    ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, s2) ==> AbSeqIn(x, AbSeqConcat(s1, s2))
    { forall x, s1, s2 { Seq_Props_concat_in_part2all_p3<X>(x, s1, s2); } }

  lemma Seq_Props_concat_in_all2part_p3<X> (x: X, s1: AbSeq<X>, s2: AbSeq<X>)
    // x in s1 + s2 && x !in s1 ==> x in s2
    ensures AbSeqIn(x, AbSeqConcat(s1, s2)) && !AbSeqIn(x, s1) ==> AbSeqIn(x, s2)
    // x in s1 + s2 && x !in s2 ==> x in s1
    ensures AbSeqIn(x, AbSeqConcat(s1, s2)) && !AbSeqIn(x, s2) ==> AbSeqIn(x, s1)
    { }
  lemma Seq_Props_concat_in_all2part<X> ()
    // x in s1 + s2 && x !in s1 ==> x in s2
    ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, AbSeqConcat(s1, s2)) && !AbSeqIn(x, s1) ==> AbSeqIn(x, s2)
    // x in s1 + s2 && x !in s2 ==> x in s1
    ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, AbSeqConcat(s1, s2)) && !AbSeqIn(x, s2) ==> AbSeqIn(x, s1)
    { forall x, s1, s2 { Seq_Props_concat_in_all2part_p3<X>(x, s1, s2); } }

  lemma Seq_Props_concat_index_part1_p3<X> (i: AbInt, s1: AbSeq<X>, s2: AbSeq<X>)
    ensures AbLeqLt(i, I0, AbSeqLen(s1)) ==> // 0 <= i < |s1|
    AbLt(i, AbSeqLen(AbSeqConcat(s1, s2))) ==> // i < |s1| < |s1 + s2|
    AbSeqIndex(i, s1) == AbSeqIndex(i, AbSeqConcat(s1, s2))
    { }
  lemma Seq_Props_concat_index_part1<X> ()
    ensures forall i: AbInt, s1: AbSeq<X>, s2: AbSeq<X> ::
    AbLeqLt(i, I0, AbSeqLen(s1)) ==> // 0 <= i < |s1|
    AbLt(i, AbSeqLen(AbSeqConcat(s1, s2))) ==> // i < |s1| < |s1 + s2|
    AbSeqIndex(i, s1) == AbSeqIndex(i, AbSeqConcat(s1, s2))
    { forall i, s1, s2 { Seq_Props_concat_index_part1_p3<X>(i, s1, s2); } }

  lemma Seq_Props_concat_index_part2_p3<X> (i: AbInt, s1: AbSeq<X>, s2: AbSeq<X>)
    ensures AbLeq(I0, AbAdd(i, AbSeqLen(s1))) ==> // 0 <= i + |s1|
      (AbLt(i, AbSeqLen(s2)) ==> AbLt(AbAdd(i, AbSeqLen(s1)), AbSeqLen(AbSeqConcat(s1, s2)))) ==> // i + |s1| < |s1 + s2|
      AbLeqLt(i, I0, AbSeqLen(s2)) ==>
      AbSeqIndex(i, s2) == AbSeqIndex(AbAdd(i, AbSeqLen(s1)), AbSeqConcat(s1, s2))
    { }
  lemma Seq_Props_concat_index_part2<X> ()
    ensures forall i: AbInt, s1: AbSeq<X>, s2: AbSeq<X> ::
      AbLeq(I0, AbAdd(i, AbSeqLen(s1))) ==> // 0 <= i + |s1|
      (AbLt(i, AbSeqLen(s2)) ==> AbLt(AbAdd(i, AbSeqLen(s1)), AbSeqLen(AbSeqConcat(s1, s2)))) ==> // i + |s1| < |s1 + s2|
      AbLeqLt(i, I0, AbSeqLen(s2)) ==>
      AbSeqIndex(i, s2) == AbSeqIndex(AbAdd(i, AbSeqLen(s1)), AbSeqConcat(s1, s2))
    { forall i, s1, s2 { Seq_Props_concat_index_part2_p3<X>(i, s1, s2); } }

  lemma Seq_Props_concat_is_orig_p2<X> (i: AbInt, s: AbSeq<X>)
    ensures AbLeqLt(i, I0, AbSeqLen(s)) ==> // 0 <= i < |s|
      s == AbSeqConcat(AbSeqSlice(I0, i, s), AbSeqSlice(i, AbSeqLen(s), s))
    { }
  lemma Seq_Props_concat_is_orig<X> ()
    ensures forall i: AbInt, s: AbSeq<X> ::
      AbLeqLt(i, I0, AbSeqLen(s)) ==> // 0 <= i < |s|
      s == AbSeqConcat(AbSeqSlice(I0, i, s), AbSeqSlice(i, AbSeqLen(s), s))
    { forall i, s { Seq_Props_concat_is_orig_p2<X> (i, s); } }

  lemma Seq_Props_in_empty_p2<X> (v: X, s: AbSeq<X>) // empty seq
    ensures AbSeqLen(s) == I0 ==> !AbSeqIn(v, s)
    { }
  lemma Seq_Props_in_empty<X> () // empty seq
    ensures forall v: X, s: AbSeq<X> :: AbSeqLen(s) == I0 ==> !AbSeqIn(v, s)
    {forall v, s { Seq_Props_in_empty_p2<X>(v, s); } }

  lemma Seq_Props_in_non_empty_p2<X> (v: X, s: AbSeq<X>) // i in s ==> |s| > 0
    ensures AbSeqIn(v, s) ==> AbLt(I0, AbSeqLen(s))
    { }
  lemma Seq_Props_in_non_empty<X> () // i in s ==> |s| > 0
    ensures forall v: X, s: AbSeq<X> :: AbSeqIn(v, s) ==> AbLt(I0, AbSeqLen(s))
    {forall v, s { Seq_Props_in_non_empty_p2<X>(v, s); } }

  lemma Seq_Props_in_idx_p2<X> (v: X, s: AbSeq<X>) // v in s ==> s[i] == v
    ensures AbSeqIn(v, s) ==>
      (exists i: AbInt :: AbLeqLt(i, I0, AbSeqLen(s)) && AbSeqIndex(i, s) == v )
  // NOTE: NEED PROVE
  lemma Seq_Props_in_idx<X> () // v in s ==> s[i] == v
    ensures forall v: X, s: AbSeq<X> :: AbSeqIn(v, s) ==>
      (exists i: AbInt :: AbLeqLt(i, I0, AbSeqLen(s)) && AbSeqIndex(i, s) == v )
    { forall v, s { Seq_Props_in_idx_p2<X>(v, s); } }

  lemma Seq_Props_slice_in_p4<X> (i: AbInt, j: AbInt, s: AbSeq<X>, v: X)
    ensures AbLeq(I0, i) && AbLeq(j, AbSeqLen(s)) && AbLeq(i, j) ==>
      AbSeqIn(v, AbSeqSlice(i, j, s)) ==> AbSeqIn(v, s)
    { }
  lemma Seq_Props_slice_in<X> ()
    ensures forall i: AbInt, j: AbInt, s: AbSeq<X>, v: X ::
      AbLeq(I0, i) && AbLeq(j, AbSeqLen(s)) && AbLeq(i, j) ==>
      AbSeqIn(v, AbSeqSlice(i, j, s)) ==> AbSeqIn(v, s)
    { forall i, j, s, v { Seq_Props_slice_in_p4<X>(i, j, s, v); } }

}

module ADT_SeqLemma {
  import opened ADT_Seq`Basic

  lemma Seq_Props_length<X> () // |s| >= 0
    ensures forall s: AbSeq<X> :: AbLeq(I0, AbSeqLen(s))
    { forall s { Seq_Props_length_p1<X> (s); } }
  
  lemma Seq_Props_concat_length<X> () // |s1 + s2| == |s1| + |s2|
    ensures forall s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqLen(AbSeqConcat(s1, s2)) == AbAdd(AbSeqLen(s1), AbSeqLen(s2))
    { forall s1, s2 { Seq_Props_concat_length_p2<X>(s1, s2); } }
  
  lemma Seq_Props_concat_in<X> () // x in s1 || x in s2 <==> x in s1 + s2
    ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, s1) || AbSeqIn(x, s2) <==> AbSeqIn(x, AbSeqConcat(s1, s2))
    { forall x, s1, s2 { Seq_Props_concat_in_p3<X>(x, s1, s2); } }
  
  lemma Seq_Props_concat_in_part2all<X> ()
    // x in s1 ==> x in s1 + s2
    ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, s1) ==> AbSeqIn(x, AbSeqConcat(s1, s2))
    // x in s2 ==> x in s1 + s2
    ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, s2) ==> AbSeqIn(x, AbSeqConcat(s1, s2))
    { forall x, s1, s2 { Seq_Props_concat_in_part2all_p3<X>(x, s1, s2); } }
  
  lemma Seq_Props_concat_in_all2part<X> ()
    // x in s1 + s2 && x !in s1 ==> x in s2
    ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, AbSeqConcat(s1, s2)) && !AbSeqIn(x, s1) ==> AbSeqIn(x, s2)
    // x in s1 + s2 && x !in s2 ==> x in s1
    ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, AbSeqConcat(s1, s2)) && !AbSeqIn(x, s2) ==> AbSeqIn(x, s1)
    { forall x, s1, s2 { Seq_Props_concat_in_all2part_p3<X>(x, s1, s2); } }
  
  lemma Seq_Props_concat_index_part1<X> ()
    ensures forall i: AbInt, s1: AbSeq<X>, s2: AbSeq<X> ::
    AbLeqLt(i, I0, AbSeqLen(s1)) ==> // 0 <= i < |s1|
    AbLt(i, AbSeqLen(AbSeqConcat(s1, s2))) ==> // i < |s1| < |s1 + s2|
    AbSeqIndex(i, s1) == AbSeqIndex(i, AbSeqConcat(s1, s2))
    { forall i, s1, s2 { Seq_Props_concat_index_part1_p3<X>(i, s1, s2); } }
  
  lemma Seq_Props_concat_index_part2<X> ()
    ensures forall i: AbInt, s1: AbSeq<X>, s2: AbSeq<X> ::
      AbLeq(I0, AbAdd(i, AbSeqLen(s1))) ==> // 0 <= i + |s1|
      (AbLt(i, AbSeqLen(s2)) ==> AbLt(AbAdd(i, AbSeqLen(s1)), AbSeqLen(AbSeqConcat(s1, s2)))) ==> // i + |s1| < |s1 + s2|
      AbLeqLt(i, I0, AbSeqLen(s2)) ==>
      AbSeqIndex(i, s2) == AbSeqIndex(AbAdd(i, AbSeqLen(s1)), AbSeqConcat(s1, s2))
    { forall i, s1, s2 { Seq_Props_concat_index_part2_p3<X>(i, s1, s2); } }
  
  lemma Seq_Props_concat_is_orig<X> ()
    ensures forall i: AbInt, s: AbSeq<X> ::
      AbLeqLt(i, I0, AbSeqLen(s)) ==> // 0 <= i < |s|
      s == AbSeqConcat(AbSeqSlice(I0, i, s), AbSeqSlice(i, AbSeqLen(s), s))
    { forall i, s { Seq_Props_concat_is_orig_p2<X> (i, s); } }
  
  lemma Seq_Props_in_empty<X> () // empty seq
    ensures forall v: X, s: AbSeq<X> :: AbSeqLen(s) == I0 ==> !AbSeqIn(v, s)
    {forall v, s { Seq_Props_in_empty_p2<X>(v, s); } }
  
  lemma Seq_Props_in_non_empty<X> () // i in s ==> |s| > 0
    ensures forall v: X, s: AbSeq<X> :: AbSeqIn(v, s) ==> AbLt(I0, AbSeqLen(s))
    {forall v, s { Seq_Props_in_non_empty_p2<X>(v, s); } }
  
  lemma Seq_Props_in_idx<X> () // v in s ==> s[i] == v
    ensures forall v: X, s: AbSeq<X> :: AbSeqIn(v, s) ==>
      (exists i: AbInt :: AbLeqLt(i, I0, AbSeqLen(s)) && AbSeqIndex(i, s) == v )
    { forall v, s { Seq_Props_in_idx_p2<X>(v, s); } }
  
  lemma Seq_Props_slice_in<X> ()
    ensures forall i: AbInt, j: AbInt, s: AbSeq<X>, v: X ::
      AbLeq(I0, i) && AbLeq(j, AbSeqLen(s)) && AbLeq(i, j) ==>
      AbSeqIn(v, AbSeqSlice(i, j, s)) ==> AbSeqIn(v, s)
    { forall i, j, s, v { Seq_Props_slice_in_p4<X>(i, j, s, v); } }
}