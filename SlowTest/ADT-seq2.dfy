include "ADT-int.dfy"
module ADT_Seq {
  export Seq_Basic 
    provides
      AAI,
      AbSeq, 
      AbSeqLen, AbSeqIndex, AbSeqConcat, AbSeqIn, AbSeqEmpty, AbSeqSingleton, AbSeqSlice, /* AbSeqInit, */
      AbSeqGetIdx, AbSeqRemove, AbSeqRemoveIdx, AbSeqUpdate,
      AbSeqSliceSame_p5, /* AbSeqInitFunc_p4, */
      AbSeqRemoveIdx_InSame_p4,
      AbSeqRemoveIdx_Part1Same_p4, AbSeqRemoveIdx_Part2Shift1_p4,
      AbSeqUpdate_Part1Same_p5, AbSeqUpdate_Part2Same_p5,

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
    requires AI.AbLt(AI.I0, i) || AI.I0 == i
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

  lemma AbSeqSliceSame_p5<X> (i: AI.AbInt, j: AI.AbInt, s: AbSeq<X>, s': AbSeq<X>, k: AI.AbInt)
    requires AI.AbLeq(AI.I0, i)
    requires AI.AbLeq(j, AbSeqLen(s))
    requires AI.AbLeq(i, j)
    requires AbSeqLen(s') == AI.AbSub(j, i) // |s'| == j-i
    requires AI.AbLeqLt(k, i, j)
    requires AI.AbLeqLt(k, AI.I0, AbSeqLen(s)) // 0 <= k <= s
    requires AI.AbLeqLt(AI.AbSub(k, i), AI.I0, AbSeqLen(s')) // 0 <= k-i <= |s'|
    requires s' == AbSeqSlice(i, j, s)
    ensures AbSeqIndex(k, s) == AbSeqIndex(AI.AbSub(k, i), s')
    { }

  function method AbSeqSlice<X> (i: AI.AbInt, j: AI.AbInt, s: AbSeq<X>) : (s' : AbSeq<X>)
    requires AI.AbLt(AI.I0, i) || AI.I0 == i
    requires AI.AbLt(j, AbSeqLen(s)) || j == AbSeqLen(s)
    requires AI.AbLt(i, j) || i == j
    ensures AbSeqLen(s') == AI.AbSub(j, i)
    ensures forall x : AI.AbInt
      // {:trigger AbSeqIndex(x, s)}
      {:trigger AbSeqIndex(AI.AbSub(x, i), s')} ::
      (AI.AbLt(i, x) || i == x) && AI.AbLt(x, j) ==> // i <= x < j
      // precond begins
      (AI.AbLt(AI.I0, x) || AI.I0 == x) && AI.AbLt(x, AbSeqLen(s)) ==>
      (AI.AbLt(AI.I0, AI.AbSub(x, i)) || AI.I0 == AI.AbSub(x, i)) && AI.AbLt(AI.AbSub(x, i), AbSeqLen(s')) ==>
      // precond ends
      AbSeqIndex(x, s) == AbSeqIndex(AI.AbSub(x, i), s')
    { s[i..j] } // s[i..j] w/ s[i] and w/o s[j]

  function method AbSeqGetIdx<X>(v: X, s: AbSeq<X>) : (i: AI.AbInt)
    requires AbSeqIn(v, s)
    ensures AI.AbLt(AI.I0, i) || AI.I0 == i
    ensures AI.AbLt(i, AbSeqLen(s))
    ensures AbSeqIndex(i, s) == v

  function method AbSeqRemove<X(!new)> (v: X, s: AbSeq<X>): (s': AbSeq<X>)
    requires AbSeqIn(v, s)
    ensures AbSeqLen(s) == AI.AbAdd(AbSeqLen(s'), AI.I1)
    ensures AbSeqLen(s') == AI.AbSub(AbSeqLen(s), AI.I1)
    // ensures forall x : X :: AbSeqIn(x, s') ==> AbSeqIn(x, s)
    ensures var k := AbSeqGetIdx(v, s);
      forall i : AI.AbInt // s[0, k) keeps
        {:trigger AbSeqIndex(i, s')} ::
        (AI.AbLt(AI.I0, i) || AI.I0 == i) && AI.AbLt(i, k) ==>
        // precond begins
        AI.AbLt(i, AbSeqLen(s)) ==>
        AI.AbLt(i, AbSeqLen(s')) ==>
        // precond ends
        AbSeqIndex(i, s) == AbSeqIndex(i, s')
    ensures var k := AbSeqGetIdx(v, s);
      forall i : AI.AbInt // s[k, |s|-1) keeps
        {:trigger AbSeqIndex(AI.AbAdd(i, AI.I1), s)}
        {:trigger AbSeqIndex(i, s')} ::
        (AI.AbLt(k, i) || k == i) && AI.AbLt(i, AbSeqLen(s')) ==>
        // precond begins
        AI.AbLt(AI.I0, i) || AI.I0 == i ==>
        AI.AbLt(AI.I0, AI.AbAdd(i, AI.I1)) ==>
        AI.AbLt(AI.AbAdd(i, AI.I1), AbSeqLen(s)) ==>
        // precond ends
        AbSeqIndex(AI.AbAdd(i, AI.I1), s) == AbSeqIndex(i, s')
  // {
  //   var k := AbSeqGetIdx(v, s);
  //   AbSeqRemoveIdx(k, s)
  // }
  
  lemma AbSeqRemoveIdx_InSame_p4<X> (k: AI.AbInt, s: AbSeq<X>, s':AbSeq<X>, v: X)
    requires AI.AbLeqLt(k, AI.I0, AbSeqLen(s))
    requires s' == AbSeqRemoveIdx(k, s)
    requires AbSeqIn(v, s')
    ensures AbSeqIn(v, s)
    { }

  // s[0, k) keeps
  lemma AbSeqRemoveIdx_Part1Same_p4<X>(k: AI.AbInt, s: AbSeq<X>, s': AbSeq<X>, i: AI.AbInt)
    requires AI.AbLeqLt(k, AI.I0, AbSeqLen(s))
    requires s' == AbSeqRemoveIdx(k, s)
    requires AI.AbLeqLt(i, AI.I0, k)
    requires AI.AbLt(i, AbSeqLen(s))
    requires AI.AbLt(i, AbSeqLen(s'))
    ensures AbSeqIndex(i, s) == AbSeqIndex(i, s')
    { }
  
  // s[k, |s|-1) shifts
  lemma AbSeqRemoveIdx_Part2Shift1_p4<X>(k: AI.AbInt, s: AbSeq<X>, s': AbSeq<X>, i: AI.AbInt)
    requires AI.AbLeqLt(k, AI.I0, AbSeqLen(s))
    requires s' == AbSeqRemoveIdx(k, s)
    requires AI.AbLeqLt(i, k, AbSeqLen(s'))
    requires AI.AbLeq(AI.I0, i)
    requires AI.AbLt(AI.I0, AI.AbAdd(i, AI.I1))
    requires AI.AbLt(AI.AbAdd(i, AI.I1), AbSeqLen(s))
    ensures AbSeqIndex(AI.AbAdd(i, AI.I1), s) == AbSeqIndex(i, s')
    { }

  function method AbSeqRemoveIdx<X(!new)> (k: AI.AbInt, s: AbSeq<X>) : (s': AbSeq<X>)
    requires (AI.AbLt(AI.I0, k) || AI.I0 == k) && AI.AbLt(k, AbSeqLen(s))
    ensures AbSeqLen(s) == AI.AbAdd(AbSeqLen(s'), AI.I1)
    ensures AbSeqLen(s') == AI.AbSub(AbSeqLen(s), AI.I1)
    // ensures forall x: X :: AbSeqIn(x, s') ==> AbSeqIn(x, s)
    ensures
      forall i : AI.AbInt // s[0, k) keeps
        {:trigger AbSeqIndex(i, s')} ::
        (AI.AbLt(AI.I0, i) || AI.I0 == i) && AI.AbLt(i, k) ==>
        // precond begins
        AI.AbLt(i, AbSeqLen(s)) ==>
        AI.AbLt(i, AbSeqLen(s')) ==>
        // precond ends
        AbSeqIndex(i, s) == AbSeqIndex(i, s')
    ensures
      forall i : AI.AbInt // s[k, |s|-1) keeps
        {:trigger AbSeqIndex(AI.AbAdd(i, AI.I1), s)}
        {:trigger AbSeqIndex(i, s')} ::
        (AI.AbLt(k, i) || k == i) && AI.AbLt(i, AbSeqLen(s')) ==>
        // precond begins
        AI.AbLt(AI.I0, i) || AI.I0 == i ==>
        AI.AbLt(AI.I0, AI.AbAdd(i, AI.I1)) ==>
        AI.AbLt(AI.AbAdd(i, AI.I1), AbSeqLen(s)) ==>
        // precond ends
        AbSeqIndex(AI.AbAdd(i, AI.I1), s) == AbSeqIndex(i, s')
    { s[ ..k ] + s[ k+1.. ] }
  // {
  //   var len := AbSeqLen(s);
  //   var half1 := AbSeqSlice(AI.I0, k, s);
  //   Props_add2sub ();
  //   Props_add_identity ();
  //   Props_notneg ();
  //   assume AbPos(AI.I1); // Props_pos (AI.I1);
  //   Props_add_pos_is_lt ();
  //   Props_lt_transitive ();
  //   if AI.AbLt(AI.AbAdd(k, AI.I1), len) then
  //     var half2 := AbSeqSlice(AI.AbAdd(k, AI.I1), len, s);
  //     // var s':= AbSeqConcat(half1, half2);
  //     Seq_Props_concat_length_p2 (half1, half2);
  //     Props_add_associative ();
  //     Props_lt_addition ();
  //     Seq_Props_concat_index_part1<X> ();
  //     // assert forall i :: // s[0, k) keeps
  //     //   (AI.AbLt(AI.I0, i) || AI.I0 == i) &&
  //     //   AI.AbLt(i, k) ==> 
  //     //   AbSeqIndex(i, s) == AbSeqIndex(i, s');
  //     Props_add_commutative ();
  //     Seq_Props_concat_index_part2<X> ();
  //     // assert forall i :: // s(k, |s|-1] keeps
  //     //   (AI.AbLt(k, i) || i == k) &&
  //     //   AI.AbLt(i, AbSeqLen(s')) ==>
  //     //   AbSeqIndex(AI.AbAdd(i, AI.I1), s) == 
  //     //   AbSeqIndex(i, s');
  //     Seq_Props_slice_in<X> ();
  //     Seq_Props_concat_in<X> ();
  //     // assert forall v :: AbSeqIn(v, s') ==> AbSeqIn(v, s);
  //     AbSeqConcat(half1, half2)
  //   else
  //     Props_lt_is_not_leq ();
  //     Props_lt2leq ();
  //     Seq_Props_slice_in<X> ();
  //     // assert forall v :: AbSeqIn(v, half1) ==> AbSeqIn(v, s);
  //     // assert forall i :: // s[0, k) keeps
  //     //   (AI.AbLt(AI.I0, i) || AI.I0 == i) &&
  //     //   AI.AbLt(i, AI.AbSub(len, AI.I1)) ==> 
  //     //   AbSeqIndex(i, s) == AbSeqIndex(i, s');
  //     // assert forall i :: // s(k, |s|-1] keeps
  //     //   (AI.AbLt(k, i) || i == k) &&
  //     //   AI.AbLt(i, AbSeqLen(s')) ==>
  //     //   AbSeqIndex(AI.AbAdd(i, AI.I1), s) == AbSeqIndex(i, s');
  //     half1
  // }

  // s[0, k) keeps
  lemma AbSeqUpdate_Part1Same_p5<X>(k: AI.AbInt, v: X, s: AbSeq<X>, s': AbSeq<X>, i: AI.AbInt)
    requires AI.AbLeqLt(k, AI.I0, AbSeqLen(s))
    requires s' == AbSeqUpdate(k, v, s)
    requires AI.AbLeqLt(i, AI.I0, k)
    requires AI.AbLt(i, AbSeqLen(s))
    requires AI.AbLt(i, AbSeqLen(s'))
    ensures AbSeqIndex(i, s) == AbSeqIndex(i, s')
    { }
  
  // s(k, |s|) keeps
  lemma AbSeqUpdate_Part2Same_p5<X>(k: AI.AbInt, v: X, s: AbSeq<X>, s': AbSeq<X>, i: AI.AbInt)
    requires AI.AbLeqLt(k, AI.I0, AbSeqLen(s))
    requires s' == AbSeqUpdate(k, v, s)
    requires AI.AbLt(k, i)
    requires AI.AbLt(i, AbSeqLen(s'))
    requires AI.AbLeqLt(i, AI.I0, AbSeqLen(s))
    ensures AbSeqIndex(i, s) == AbSeqIndex(i, s')
    { }

  function method AbSeqUpdate<X> (k: AI.AbInt, v: X, s: AbSeq<X>): (s': AbSeq<X>)
    requires (AI.AbLt(AI.I0, k) || AI.I0 == k) && AI.AbLt(k, AbSeqLen(s))
    ensures AbSeqLen(s) == AbSeqLen(s')
    ensures AbSeqIndex(k, s') == v
    ensures
      forall i : AI.AbInt // s[0, k) keeps
        {:trigger AbSeqIndex(i, s')} ::
        (AI.AbLt(AI.I0, i) || AI.I0 == i) && AI.AbLt(i, k) ==>
        // precond begins
        AI.AbLt(i, AbSeqLen(s)) ==>
        AI.AbLt(i, AbSeqLen(s')) ==>
        // precond ends
        AbSeqIndex(i, s) == AbSeqIndex(i, s')
    ensures
      forall i : AI.AbInt // s(k, |s|) keeps
        {:trigger AbSeqIndex(i, s')} ::
        AI.AbLt(k, i) && AI.AbLt(i, AbSeqLen(s)) ==>
        // precond begins
        AI.AbLt(AI.I0, i) || AI.I0 == i ==>
        AI.AbLt(i, AbSeqLen(s')) ==>
        // precond ends
        AbSeqIndex(i, s) == AbSeqIndex(i, s')
    { s[ k := v ] }
  // {
  //   var len := AbSeqLen(s);
  //   var half1 := AbSeqSlice(AI.I0, k, s);
  //   Props_add2sub ();
  //   Props_add_identity ();
  //   Props_notneg ();
  //   assume AbPos(AI.I1); // Props_pos (AI.I1);
  //   Props_add_pos_is_lt ();
  //   Props_lt_transitive ();
  //   Props_add_commutative ();
  //   if AI.AbLt(AI.AbAdd(k, AI.I1), len) then
  //     var half2 := AbSeqSlice(AI.AbAdd(k, AI.I1), len, s);
  //     var half1' := AbSeqConcat(half1, AbSeqSingleton(v));
  //     Seq_Props_concat_length_p2 (half1, AbSeqSingleton(v));
  //     Seq_Props_concat_length_p2 (half1', half2);
  //     // var s' := AbSeqConcat(half1', half2);
  //     // assert len == AbSeqLen(s');
  //     Props_lt_addition ();
  //     Seq_Props_concat_index_part1<X> ();
  //     // assert forall i :: // s[0, k) keeps
  //     //   (AI.AbLt(AI.I0, i) || AI.I0 == i) &&
  //     //   AI.AbLt(i, k) ==>
  //     //   AbSeqIndex(i, s) == AbSeqIndex(i, s');
  //     // Seq_Props_concat_is_orig<X> ();
  //     Seq_Props_concat_is_orig_p2 (AI.AbAdd(k, AI.I1), s);
  //     Seq_Props_concat_index_part2<X> ();
  //     // Seq_Props_concat_index_part2_param (AI.I0, half1, AbSeqSingleton(v));
  //     // assert AbSeqIndex(k, half1') == v;
      
  //     // assert forall i :: // s(k, |s|-1] keeps
  //     //   AI.AbLt(k, i) && AI.AbLt(i, AbSeqLen(s)) ==>
  //     //   AbSeqIndex(i, s) == AbSeqIndex(AI.AbSub(i, AI.AbAdd(k, AI.I1)), half2);
  //     // assert forall i :: // s(k, |s|-1] keeps
  //     //   AI.AbLt(k, i) &&
  //     //   AI.AbLt(i, AbSeqLen(s')) ==>
  //     //   AbSeqIndex(i, s) == AbSeqIndex(i, s');
  //     AbSeqConcat(half1', half2)
  //   else
  //     Props_lt_is_not_leq_p2 (AI.AbAdd(k, AI.I1), len);
  //     Props_lt2leq ();
  //     // var s' := AbSeqConcat(half1, AbSeqSingleton(v));
  //     Seq_Props_concat_length_p2 (half1, AbSeqSingleton(v));
  //     // assert AbSeqLen(s') == len;
  //     Seq_Props_concat_index_part1<X> ();
  //     // assert forall i :: // s[0, k) keeps
  //     //   (AI.AbLt(AI.I0, i) || AI.I0 == i) &&
  //     //   AI.AbLt(i, k) ==>
  //     //   AbSeqIndex(i, s) == AbSeqIndex(i, s');
  //     // assert forall i :: // s(k, |s|-1] keeps
  //     //   AI.AbLt(k, i) &&
  //     //   AI.AbLt(i, AbSeqLen(s')) ==>
  //     //   AbSeqIndex(i, s) == AbSeqIndex(i, s');
  //     Seq_Props_concat_index_part2<X> ();
  //     // assert AbSeqIndex(k, s') == v;
  //     AbSeqConcat(half1, AbSeqSingleton(v))
  //  }

  function method AbSeqInsertIdx<X(!new)> (k: AI.AbInt, v: X, s: AbSeq<X>) : (s': AbSeq<X>)
    requires (AI.AbLt(AI.I0, k) || AI.I0 == k) && AI.AbLt(k, AbSeqLen(s))
    ensures AbSeqLen(s') == AI.AbAdd(AbSeqLen(s), AI.I1)
    ensures AbSeqIndex(k, s') == v
    ensures
      forall i : AI.AbInt // s[0, k) keeps
        {:trigger AbSeqIndex(i, s')} ::
        (AI.AbLt(AI.I0, i) || AI.I0 == i) && AI.AbLt(i, k) ==>
        // precond begins
        AI.AbLt(i, AbSeqLen(s)) ==>
        AI.AbLt(i, AbSeqLen(s')) ==>
        // precond ends
        AbSeqIndex(i, s') == AbSeqIndex(i, s)
    ensures
      forall i : AI.AbInt // s[k, |s|) keeps
        {:trigger AbSeqIndex(AI.AbAdd(i, AI.I1), s)}
        {:trigger AbSeqIndex(i, s')} ::
        (AI.AbLt(k, i) || k == i) && AI.AbLt(i, AbSeqLen(s)) ==>
        // precond begins
        AI.AbLt(AI.I0, i) || AI.I0 == i ==>
        AI.AbLt(AI.I0, AI.AbAdd(i, AI.I1)) ==>
        AI.AbLt(AI.AbAdd(i, AI.I1), AbSeqLen(s')) ==>
        // precond ends
        AbSeqIndex(i, s) == AbSeqIndex(AI.AbAdd(i, AI.I1), s')
  { s[..k] + [v] + s[k..] }

  lemma Seq_Props_length_p1<X> (s: AbSeq<X>) // |s| >= 0
    ensures AI.AbLt(AI.I0, AbSeqLen(s)) || AI.I0 == AbSeqLen(s)
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
    requires (AI.AbLt(AI.I0, i) || AI.I0 == i) && AI.AbLt(i, AbSeqLen(s1)) // 0 <= i < |s1|
    requires AI.AbLt(i, AbSeqLen(AbSeqConcat(s1, s2))) // i < |s1| < |s1 + s2|
    ensures AbSeqIndex(i, s1) == AbSeqIndex(i, AbSeqConcat(s1, s2))
    { }

  lemma Seq_Props_concat_index_part2_p3<X> (i: AI.AbInt, s1: AbSeq<X>, s2: AbSeq<X>)
    requires (AI.AbLt(AI.I0, i) || AI.I0 == i) && AI.AbLt(i, AbSeqLen(s2)) // 0 <= i < |s2|
    requires AI.AbLt(AI.I0, AI.AbAdd(i, AbSeqLen(s1))) || AI.I0 == AI.AbAdd(i, AbSeqLen(s1)) // 0 <= i + |s1|
    requires AI.AbLt(AI.AbAdd(i, AbSeqLen(s1)), AbSeqLen(AbSeqConcat(s1, s2)))  // i + |s1| < |s1 + s2|
    ensures AbSeqIndex(i, s2) == AbSeqIndex(AI.AbAdd(i, AbSeqLen(s1)), AbSeqConcat(s1, s2))
    { }

  lemma Seq_Props_concat_is_orig_p2<X> (i: AI.AbInt, s: AbSeq<X>)
    requires (AI.AbLt(AI.I0, i) || AI.I0 == i) && AI.AbLt(i, AbSeqLen(s)) // 0 <= i < |s|
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
    ensures exists i: AI.AbInt ::
      (AI.AbLt(AI.I0, i) || AI.I0 == i) && AI.AbLt(i, AbSeqLen(s))
      && AbSeqIndex(i, s) == v
    { ghost var k :| 0 <= k < |s| && s[k] == v;
      // match the "exists" pattern
      assert (AI.AbLt(AI.I0, k) || AI.I0 == k) && AI.AbLt(k, AbSeqLen(s)) && AbSeqIndex(k, s) == v; }
  
  lemma Seq_Props_idx_in_p2<X> (k: AI.AbInt, s: AbSeq<X>) // s[k] in s
    requires (AI.AbLt(AI.I0, k) || AI.I0 == k) && AI.AbLt(k, AbSeqLen(s)) // 0 <= k < |s|
    ensures AbSeqIn(AbSeqIndex(k, s), s)
    { }
  
  lemma Seq_Props_slice_in_p4<X> (i: AI.AbInt, j: AI.AbInt, s: AbSeq<X>, v: X)
    requires AI.AbLt(AI.I0, i) || AI.I0 == i 
    requires AI.AbLt(j, AbSeqLen(s)) || j == AbSeqLen(s)
    requires AI.AbLt(i, j) || i == j
    ensures AbSeqIn(v, AbSeqSlice(i, j, s)) ==> AbSeqIn(v, s)
    { }
}

import opened ADT`Basic
import opened ADT_Seq`Seq_Basic

function method AbSeqInit<X> (len: AbInt, func : AbInt --> X) : (s: AbSeq<X>)
  requires AbLt(I0, len) || I0 == len
  requires forall i : AbInt :: (AbLt(I0, i) || I0 == i) && AbLt(i, len) ==> func.requires(i)
  ensures AbSeqLen(s) == len
  ensures forall i : AbInt
    {:trigger AbSeqIndex(i, s)} {: trigger func(i)} ::
    (AbLt(I0, i) || I0 == i) && AbLt(i, len) ==> AbSeqIndex(i, s) == func(i)

function method AbSeqResize<X>(s: AbSeq<X>, newlen: AbInt, a: X) : (s': AbSeq<X>)
  requires AbLt(I0, newlen) || I0 == newlen
  ensures AbSeqLen(s') == newlen
  ensures forall j : AbInt
    // {:trigger AbSeqIndex(j, s)}
    {:trigger AbSeqIndex(j, s')} ::
    (AbLt(I0, j) || I0 == j) && AbLt(j, newlen) ==>
    AbSeqIndex(j, s') == (if AbLt(j, AbSeqLen(s)) then AbSeqIndex(j, s) else a) 

lemma AbSeqSliceSame<X> (i: AbInt, j: AbInt, s: AbSeq<X>, s': AbSeq<X>)
  requires AbLeq(I0, i)
  requires AbLeq(j, AbSeqLen(s))
  requires AbLeq(i, j)
  requires AbSeqLen(s') == AbSub(j, i) // |s'| == j-i
  requires s' == AbSeqSlice(i, j, s)
  ensures forall k : AbInt
    {:trigger AbSeqIndex(k, s)}
    {:trigger AbSeqIndex(AbSub(k, i), s')} ::  
    AbLeqLt(k, i, j) && 
    AbLeqLt(k, I0, AbSeqLen(s)) && // 0 <= k <= s
    AbLeqLt(AbSub(k, i), I0, AbSeqLen(s')) // 0 <= k-i <= |s'|
    ==> AbSeqIndex(k, s) == AbSeqIndex(AbSub(k, i), s')
  { forall k | AbLeqLt(k, i, j) && 
    AbLeqLt(k, I0, AbSeqLen(s)) && // 0 <= k <= s
    AbLeqLt(AbSub(k, i), I0, AbSeqLen(s')) // 0 <= k-i <= |s'|
    { AbSeqSliceSame_p5(i, j, s, s', k); } }

lemma AbSeqRemoveIdx_InSame<X> (s: AbSeq<X>, s':AbSeq<X>)
  ensures forall k: AbInt, v: X ::
    AbLeqLt(k, I0, AbSeqLen(s)) &&
    s' == AbSeqRemoveIdx(k, s) &&
    AbSeqIn(v, s') ==> AbSeqIn(v, s)
  { forall k, v | AbLeqLt(k, I0, AbSeqLen(s)) &&
    s' == AbSeqRemoveIdx(k, s) && AbSeqIn(v, s')
    {AbSeqRemoveIdx_InSame_p4(k, s, s', v); } }

lemma AbSeqRemoveIdx_Part1Same<X>(k: AbInt, s: AbSeq<X>, s': AbSeq<X>)
  // s[0, k) keeps
  requires AbLeqLt(k, I0, AbSeqLen(s))
  requires s' == AbSeqRemoveIdx(k, s)
  ensures forall i : AbInt
    {:trigger AbSeqIndex(i, s')} ::
    AbLeqLt(i, I0, k) && 
    AbLt(i, AbSeqLen(s)) && AbLt(i, AbSeqLen(s'))
     ==> AbSeqIndex(i, s) == AbSeqIndex(i, s')
  { forall i | AbLeqLt(i, I0, k) && 
    AbLt(i, AbSeqLen(s)) && AbLt(i, AbSeqLen(s'))
    { AbSeqRemoveIdx_Part1Same_p4(k, s, s', i); } }

lemma AbSeqRemoveIdx_Part2Shift1<X>(k: AbInt, s: AbSeq<X>, s': AbSeq<X>)
  // s[k, |s|-1) shifts
  requires AbLeqLt(k, I0, AbSeqLen(s))
  requires s' == AbSeqRemoveIdx(k, s)
  ensures forall i : AbInt
    {:trigger AbSeqIndex(AbAdd(i, I1), s)}
    {:trigger AbSeqIndex(i, s')} ::
    AbLeqLt(i, k, AbSeqLen(s')) && AbLeq(I0, i) &&
    AbLt(I0, AbAdd(i, I1)) && AbLt(AbAdd(i, I1), AbSeqLen(s))
    ==> AbSeqIndex(AbAdd(i, I1), s) == AbSeqIndex(i, s')
  { forall i | AbLeqLt(i, k, AbSeqLen(s')) && AbLeq(I0, i) &&
    AbLt(I0, AbAdd(i, I1)) && AbLt(AbAdd(i, I1), AbSeqLen(s))
    { AbSeqRemoveIdx_Part2Shift1_p4(k, s, s', i); } }

lemma AbSeqUpdate_Part1Same<X>(k: AbInt, v: X, s: AbSeq<X>, s': AbSeq<X>)
  // s[0, k) keeps
  requires AbLeqLt(k, I0, AbSeqLen(s))
  requires s' == AbSeqUpdate(k, v, s)
  ensures forall i : AbInt
    {:trigger AbSeqIndex(i, s')} ::
    AbLeqLt(i, I0, k) && 
    AbLt(i, AbSeqLen(s)) && AbLt(i, AbSeqLen(s'))
     ==> AbSeqIndex(i, s) == AbSeqIndex(i, s')
  { forall i | AbLeqLt(i, I0, k) && 
    AbLt(i, AbSeqLen(s)) && AbLt(i, AbSeqLen(s'))
    { AbSeqUpdate_Part1Same_p5(k, v, s, s', i); } }

lemma AbSeqUpdate_Part2Same<X>(k: AbInt, v: X, s: AbSeq<X>, s': AbSeq<X>)
  // s(k, |s|) keeps
  requires AbLeqLt(k, I0, AbSeqLen(s))
  requires s' == AbSeqUpdate(k, v, s)
  ensures forall i : AbInt
    {:trigger AbSeqIndex(i, s')} ::
    AbLt(k, i) && AbLt(i, AbSeqLen(s')) && 
    AbLeqLt(i, I0, AbSeqLen(s))
    ==> AbSeqIndex(i, s) == AbSeqIndex(i, s')
  { forall i | AbLt(k, i) && AbLt(i, AbSeqLen(s')) && 
    AbLeqLt(i, I0, AbSeqLen(s))
    { AbSeqUpdate_Part2Same_p5(k, v, s, s', i); } }

lemma Seq_Props_length<X> () // |s| >= 0
  ensures forall s: AbSeq<X> :: AbLt(I0, AbSeqLen(s)) || I0 == AbSeqLen(s)
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
  (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(s1)) ==> // 0 <= i < |s1|
  AbLt(i, AbSeqLen(AbSeqConcat(s1, s2))) ==> // i < |s1| < |s1 + s2|
  AbSeqIndex(i, s1) == AbSeqIndex(i, AbSeqConcat(s1, s2))
  { forall i, s1, s2 | (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(s1)) && 
      AbLt(i, AbSeqLen(AbSeqConcat(s1, s2)))
    { Seq_Props_concat_index_part1_p3<X>(i, s1, s2); } }

lemma Seq_Props_concat_index_part2<X> ()
  ensures forall i: AbInt, s1: AbSeq<X>, s2: AbSeq<X>
    {:trigger AbSeqIndex(AbAdd(i, AbSeqLen(s1)), AbSeqConcat(s1, s2))} ::
    (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(s2)) ==>
    AbLt(I0, AbAdd(i, AbSeqLen(s1))) || I0 == AbAdd(i, AbSeqLen(s1)) ==> // 0 <= i + |s1|
    AbLt(AbAdd(i, AbSeqLen(s1)), AbSeqLen(AbSeqConcat(s1, s2))) ==> // i + |s1| < |s1 + s2|
    AbSeqIndex(i, s2) == AbSeqIndex(AbAdd(i, AbSeqLen(s1)), AbSeqConcat(s1, s2))
  { forall i, s1, s2 | (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(s2)) && 
      (AbLt(I0, AbAdd(i, AbSeqLen(s1))) || I0 == AbAdd(i, AbSeqLen(s1))) && 
      AbLt(AbAdd(i, AbSeqLen(s1)), AbSeqLen(AbSeqConcat(s1, s2)))
    { Seq_Props_concat_index_part2_p3<X>(i, s1, s2); } }

lemma Seq_Props_concat_is_orig<X> ()
  ensures forall i: AbInt, s: AbSeq<X>
    {:trigger AbSeqSlice(I0, i, s)}
    {:trigger AbSeqSlice(i, AbSeqLen(s), s)} ::
    (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(s)) ==> // 0 <= i < |s|
    s == AbSeqConcat(AbSeqSlice(I0, i, s), AbSeqSlice(i, AbSeqLen(s), s))
  { forall i, s | (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(s))
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
    (exists i: AbInt :: (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(s)) &&
    AbSeqIndex(i, s) == v )
  { forall v, s | AbSeqIn(v, s)
    { Seq_Props_in_idx_p2<X>(v, s); } }

lemma Seq_Props_idx_in<X> () // v in s ==> s[i] == v
  ensures forall k: AbInt, s: AbSeq<X>
    {:trigger AbSeqIndex(k, s)} ::
    (AbLt(I0, k) || I0 == k) && AbLt(k, AbSeqLen(s)) ==>
    AbSeqIn(AbSeqIndex(k, s), s)
  { forall k, s | (AbLt(I0, k) || I0 == k) && AbLt(k, AbSeqLen(s))
    {Seq_Props_idx_in_p2<X>(k, s); } }

lemma Seq_Props_slice_in<X> ()
  ensures forall i: AbInt, j: AbInt, s: AbSeq<X>, v: X
    {:trigger AbSeqIn(v, AbSeqSlice(i, j, s))} ::
    (AbLt(I0, i) || I0 == i) &&
    (AbLt(j, AbSeqLen(s)) || j == AbSeqLen(s)) &&
    (AbLt(i, j) || i == j) ==>
    AbSeqIn(v, AbSeqSlice(i, j, s)) ==> AbSeqIn(v, s)
  { forall i, j, s, v | (AbLt(I0, i) || I0 == i) &&
    (AbLt(j, AbSeqLen(s)) || j == AbSeqLen(s)) &&
    (AbLt(i, j) || i == j)
    { Seq_Props_slice_in_p4<X>(i, j, s, v); } }