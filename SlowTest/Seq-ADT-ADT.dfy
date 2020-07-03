type AbInt(==)
datatype Nat = Z | S(Nat)
const I0 : AbInt := int2adt(0)
const I1 : AbInt := int2adt(1)
function method adt2dt (a: AbInt) : Nat
lemma Props_adt_dt_lt (x: AbInt, y: AbInt)
  requires AbLt(x, y)
  ensures adt2dt(x) < adt2dt(y)
function method int2adt (n: int) : AbInt
predicate AbIsZero (n: AbInt) { n == I0 }
predicate AbPos (n: AbInt) { !AbIsZero(n) }
// predicate AbNonNeg (n: AbInt) { true }
function method AbLt(n: AbInt, m: AbInt) : bool
// function method AbInc(n: AbInt) : AbInt
function method AbAdd(n: AbInt, m: AbInt) : AbInt
// function method AbDec(n: AbInt) : AbInt
function method AbSub(n: AbInt, m: AbInt) : AbInt

lemma Props_int_pos(a: int)
  ensures AbPos(int2adt(a))
lemma Props_all_nonneg ()
  ensures forall x :: AbLt(I0, x) || I0 == x
lemma Props_add_commutative () // x + y == y + x
  ensures forall x, y :: AbAdd(x, y) == AbAdd(y, x);
lemma Props_add_associative () // (x + y) + z == x + (y + z)
  ensures forall x, y, z :: AbAdd(AbAdd(x, y), z) == AbAdd(x, AbAdd(y, z))
lemma Props_add_identity () // x + 0 == 0 + x == x
  ensures forall x :: AbAdd(x, I0) == x
lemma Props_add_pos_is_pos () // x + Positive is Positive
  ensures forall x, a :: AbPos(a) ==> AbPos(AbAdd(x, a))
lemma Props_add_pos_is_lt () // x < x + Positive
  ensures forall x, a :: AbPos(a) ==> AbLt(x, AbAdd(x, a));
lemma Props_add_lt_is_lt () // x + a == y + b && a < b ==> x > y
  ensures forall x, y, a, b :: AbAdd(x, a) == AbAdd(y, b) ==> (AbLt(a, b) <==> AbLt(y, x))
lemma Props_add2sub () // x + y == z ==> x = z - y && y = z - x
  ensures forall x, y, z :: AbAdd(x, y) == z <==> AbSub(z, y) == x
  ensures forall x, y, z :: AbAdd(x, y) == z <==> AbSub(z, x) == y
  ensures forall x, y :: AbAdd(AbSub(x, y), y) == x
  ensures forall x, y :: AbSub(AbAdd(x, y), y) == x
lemma Props_gt2geq ()
  ensures forall x, y :: AbLt(x, y) <==> AbLt(AbAdd(x, I1), y) || AbAdd(x, I1) == y
  ensures forall x, y :: AbLt(x, y) <==> AbLt(x, AbSub(y, I1)) || x == AbSub(y, I1)

lemma Props_lt_transitive () // x < y < z
  ensures forall x, y, z :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
lemma Props_lt_addition () // a < b ==> x + a < x + b
  ensures forall x, a, b:: AbLt(a, b) ==> AbLt(AbAdd(x, a), AbAdd(x, b))
  ensures forall x, a, b:: AbLt(a, b) ==> AbLt(AbSub(a, x), AbSub(b, x))
lemma Props_ltgteq () // x < y or x > y or x == y
  ensures forall x, y :: AbLt(x, y) || AbLt(y, x) || x == y

type AbSeq<X>
function method AbSeqLen<X> (s: AbSeq<X>) : AbInt
function method AbSeqIndex<X> (i: AbInt, s: AbSeq<X>) : X
  requires AbLt(I0, i) || I0 == i
  requires AbLt(i, AbSeqLen(s))
  ensures AbSeqIn(AbSeqIndex(i, s), s)

function method AbSeqConcat<X> (s1: AbSeq<X>, s2: AbSeq<X>) : AbSeq<X>
function method AbSeqIn<X> (v: X, s: AbSeq<X>) : bool

function method AbSeqEmpty<X> (): (s: AbSeq<X>)
  ensures AbSeqLen(s) == I0

function method AbSeqSingleton<X(!new)> (v: X): (s: AbSeq<X>)
  ensures AbSeqLen(s) == I1
  ensures AbLt(I0, I1) ==> AbSeqIndex(I0, s) == v
  // ensures AbSeqIn(v, s)
  // ensures forall x :: x != v ==> !AbSeqIn(x, s)

function method AbSeqSlice<X> (i: AbInt, j: AbInt, s: AbSeq<X>) : (s' : AbSeq<X>)
  requires AbLt(I0, i) || i == I0
  requires AbLt(j, AbSeqLen(s)) || j == AbSeqLen(s)
  requires AbLt(i, j) || i == j
  ensures AbSeqLen(s') == AbSub(j, i)
  // Props_lt_transitive ();
  ensures forall x :: AbLt(x, j) ==> AbLt(x, AbSeqLen(s))
  ensures forall x :: (AbLt(i, x) || i == x) ==> (AbLt(I0, x) || I0 == x)
  // Props_add2sub (); Props_lt_addition ();
  ensures forall x, y :: AbLt(x, y) ==> AbLt(AbSub(x, i), AbSub(y, i))
  ensures forall x :: (AbLt(i, x) || i == x) ==> (AbLt(I0, AbSub(x, i)) || I0 == AbSub(x, i))
  ensures forall x :: (AbLt(i, x) || i == x) && AbLt(x, j) ==> 
    AbSeqIndex(x, s) == 
    AbSeqIndex(AbSub(x, i), s') // s[i..j] w/ s[i] and w/o s[j]

function method AbSeqGetIdx<X>(v: X, s: AbSeq<X>) : (i: AbInt)
  requires AbSeqIn(v, s)
  ensures AbLt(I0, i) || I0 == i
  ensures AbLt(i, AbSeqLen(s))
  ensures AbSeqIndex(i, s) == v
  // Seq_Props_in_idx ();
  // while (
  //   (AbLt(I0, i) || I0 == i) &&
  //   AbLt(i, AbSeqLen(s)) && 
  //   AbSeqIndex(i, s) != v)
  //   decreases adt2dt(AbSub(AbSeqLen(s), i))
  // {
  //   Props_int_pos(1);
  //   Props_add2sub ();
  //   Props_add_pos_is_lt ();
  //   Props_add_lt_is_lt ();
  //   Props_adt_dt_lt(AbSub(AbSeqLen(s), AbAdd(i, I1)), AbSub(AbSeqLen(s), i)); // decrease
  //   i := AbAdd(i, I1);
  // }

lemma Seq_Props_length<X> () // |s| >= 0
  ensures forall s: AbSeq<X> :: AbSeqLen(s) == I0 || AbLt(I0, AbSeqLen(s))

lemma Seq_Props_concat_length<X> () // |s1 + s2| == |s1| + |s2|
  ensures forall s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqLen(AbSeqConcat(s1, s2)) == AbAdd(AbSeqLen(s1), AbSeqLen(s2))
lemma Seq_Props_concat_length_param<X> (s1: AbSeq<X>, s2: AbSeq<X>) // |s1 + s2| == |s1| + |s2|
  ensures AbSeqLen(AbSeqConcat(s1, s2)) == AbAdd(AbSeqLen(s1), AbSeqLen(s2))
lemma Seq_Props_concat_in<X> () // x in s1 || x in s2 <==> x in s1 + s2
  ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, s1) || AbSeqIn(x, s2) <==> AbSeqIn(x, AbSeqConcat(s1, s2))
lemma Seq_Props_concat_in_half_all<X> ()
  // x in s1 ==> x in s1 + s2
  ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, s1) ==> AbSeqIn(x, AbSeqConcat(s1, s2))
  // x in s2 ==> x in s1 + s2
  ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, s2) ==> AbSeqIn(x, AbSeqConcat(s1, s2))
lemma Seq_Props_concat_in_half<X> ()
  // x in s1 + s2 && x !in s1 ==> x in s2
  ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, AbSeqConcat(s1, s2)) && !AbSeqIn(x, s1) ==> AbSeqIn(x, s2)
  // x in s1 + s2 && x !in s2 ==> x in s1
  ensures forall x: X, s1: AbSeq<X>, s2: AbSeq<X> :: AbSeqIn(x, AbSeqConcat(s1, s2)) && !AbSeqIn(x, s2) ==> AbSeqIn(x, s1)

lemma Seq_Props_concat_index_half_1st<X> ()
  ensures forall i: AbInt, s1: AbSeq<X>, s2: AbSeq<X> ::
  (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(s1)) ==> // 0 <= i < |s1|
  AbLt(i, AbSeqLen(AbSeqConcat(s1, s2))) ==> // i < |s1| < |s1 + s2|
  AbSeqIndex(i, s1) == AbSeqIndex(i, AbSeqConcat(s1, s2))

lemma Seq_Props_concat_index_half_2nd<X> ()
  ensures forall i: AbInt, s1: AbSeq<X>, s2: AbSeq<X> ::
    (AbLt(I0, AbAdd(i, AbSeqLen(s1))) || I0 == AbAdd(i, AbSeqLen(s1))) ==> // 0 <= i + |s1|
    (AbLt(i, AbSeqLen(s2)) ==> AbLt(AbAdd(i, AbSeqLen(s1)), AbSeqLen(AbSeqConcat(s1, s2)))) ==> // i + |s1| < |s1 + s2|
    (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(s2)) ==>
    AbSeqIndex(i, s2) == AbSeqIndex(AbAdd(i, AbSeqLen(s1)), AbSeqConcat(s1, s2))
// lemma Seq_Props_concat_index_half_2nd_param<X> (i: AbInt, s1: AbSeq<X>, s2: AbSeq<X>)
//   ensures
//     (AbLt(I0, AbAdd(i, AbSeqLen(s1))) || I0 == AbAdd(i, AbSeqLen(s1))) ==> // 0 <= i + |s1|
//     (AbLt(i, AbSeqLen(s2)) ==> AbLt(AbAdd(i, AbSeqLen(s1)), AbSeqLen(AbSeqConcat(s1, s2)))) ==> // i + |s1| < |s1 + s2|
//     (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(s2)) ==>
//     AbSeqIndex(i, s2) == AbSeqIndex(AbAdd(i, AbSeqLen(s1)), AbSeqConcat(s1, s2))

lemma Seq_Props_concat_is_orig<X> ()
  ensures forall i: AbInt, s: AbSeq<X> ::
    (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(s)) ==> // 0 <= i < |s|
    s == AbSeqConcat(AbSeqSlice(I0, i, s), AbSeqSlice(i, AbSeqLen(s), s))
// lemma Seq_Props_concat_is_orig_param<X> (i: AbInt, s: AbSeq<X>)
//   ensures
//     (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(s)) ==> // 0 <= i < |s|
//     s == AbSeqConcat(AbSeqSlice(I0, i, s), AbSeqSlice(i, AbSeqLen(s), s))


lemma Seq_Props_in_empty<X> () // empty seq
  ensures forall v: X, s: AbSeq<X> :: AbSeqLen(s) == I0 ==> !AbSeqIn(v, s)
lemma Seq_Props_in_non_empty<X> () // i in s ==> |s| > 0
  ensures forall v: X, s: AbSeq<X> :: AbSeqIn(v, s) ==> AbLt(I0, AbSeqLen(s))
lemma Seq_Props_in_idx<X> () // v in s ==> s[i] == v
  ensures forall v: X, s: AbSeq<X> :: AbSeqIn(v, s) ==>
    (exists i: AbInt :: (AbLt(I0, i) || I0 == i) && AbLt(i, AbSeqLen(s)) && AbSeqIndex(i, s) == v )

lemma Seq_Props_slice_in<X> ()
  ensures forall i: AbInt, j: AbInt, s: AbSeq<X>, v: X ::
    (AbLt(I0, i) || i == I0) && (AbLt(j, AbSeqLen(s)) || j == AbSeqLen(s)) && (AbLt(i, j) || i == j) ==>
    AbSeqIn(v, AbSeqSlice(i, j, s)) ==> AbSeqIn(v, s)

function method AbSeqRemove<X(!new)> (v: X, s: AbSeq<X>): (s': AbSeq<X>)
  requires AbSeqIn(v, s)
  ensures AbSeqLen(s) == AbAdd(AbSeqLen(s'), I1)
  ensures AbSeqLen(s') == AbSub(AbSeqLen(s), I1)
  ensures forall v :: AbSeqIn(v, s') ==> AbSeqIn(v, s)
  ensures var k := AbSeqGetIdx(v, s);
    forall i :: // s[0, k) keeps
      (AbLt(I0, i) || I0 == i) && AbLt(i, k) ==>
      // precond begins
      (AbLt(i, AbSeqLen(s))) ==>
      (AbLt(i, AbSeqLen(s'))) ==>
      // precond ends
      AbSeqIndex(i, s) == AbSeqIndex(i, s')
  ensures var k := AbSeqGetIdx(v, s);
    forall i :: // s(k, |s|-1] keeps
      AbLt(k, i) && AbLt(i, AbSeqLen(s')) ==>
      // precond begins
      AbLt(I0, i) || I0 == i ==>
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
      (AbLt(I0, i) || I0 == i) && AbLt(i, k) ==>
      // precond begins
      AbLt(i, AbSeqLen(s)) ==>
      AbLt(i, AbSeqLen(s')) ==>
      // precond ends
      AbSeqIndex(i, s) == AbSeqIndex(i, s')
  ensures
    forall i :: // s(k, |s|-1] keeps
      AbLt(k, i) &&
      AbLt(i, AbSeqLen(s')) ==>
      // precond begins
      AbLt(I0, i) || I0 == i ==>
      AbLt(I0, AbAdd(i, I1)) ==>
      AbLt(AbAdd(i, I1), AbSeqLen(s)) ==>
      // precond ends
      AbSeqIndex(AbAdd(i, I1), s) == AbSeqIndex(i, s')
{
  var len := AbSeqLen(s);
  var half1 := AbSeqSlice(I0, k, s);
  Props_add2sub ();
  Props_add_identity ();
  Props_all_nonneg (); Props_int_pos(1);
  Props_add_pos_is_lt ();
  Props_lt_transitive ();
  if AbLt(AbAdd(k, I1), len) then
    var half2 := AbSeqSlice(AbAdd(k, I1), len, s);
    // var s':= AbSeqConcat(half1, half2);
    Seq_Props_concat_length_param (half1, half2);
    Props_add_associative ();
    Props_lt_addition ();
    Seq_Props_concat_index_half_1st<X> ();
    // assert forall i :: // s[0, k) keeps
    //   (AbLt(I0, i) || I0 == i) &&
    //   AbLt(i, k) ==> 
    //   AbSeqIndex(i, s) == AbSeqIndex(i, s');
    Props_add_commutative ();
    Seq_Props_concat_index_half_2nd<X> ();
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
    Props_ltgteq ();
    Props_gt2geq ();
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
  requires AbLt(I0, k) || I0 == k
  ensures AbSeqLen(s) == AbSeqLen(s')
  ensures AbSeqIndex(k, s') == v
  ensures
    forall i :: // s[0, k) keeps
      (AbLt(I0, i) || I0 == i) && AbLt(i, k) ==>
      // precond begins
      AbLt(i, AbSeqLen(s)) ==>
      AbLt(i, AbSeqLen(s')) ==>
      // precond ends
      AbSeqIndex(i, s) == AbSeqIndex(i, s')
  ensures
    forall i :: // s(k, |s|-1] keeps
      AbLt(k, i) && AbLt(i, AbSeqLen(s')) ==>
      // precond begins
      AbLt(I0, i) || I0 == i ==>
      AbLt(i, AbSeqLen(s)) ==>
      // precond ends
      AbSeqIndex(i, s) == AbSeqIndex(i, s')
{
  var len := AbSeqLen(s);
  var half1 := AbSeqSlice(I0, k, s);
  Props_add2sub ();
  Props_add_identity ();
  Props_all_nonneg (); Props_int_pos(1);
  Props_add_pos_is_lt ();
  Props_lt_transitive ();
  Props_add_commutative ();
  if AbLt(AbAdd(k, I1), len) then
    var half2 := AbSeqSlice(AbAdd(k, I1), len, s);
    var half1' := AbSeqConcat(half1, AbSeqSingleton(v));
    Seq_Props_concat_length_param (half1, AbSeqSingleton(v));
    Seq_Props_concat_length_param (half1', half2);
    // var s' := AbSeqConcat(half1', half2);
    // assert len == AbSeqLen(s');
    Props_lt_addition ();
    Seq_Props_concat_index_half_1st<X> ();
    // assert forall i :: // s[0, k) keeps
    //   (AbLt(I0, i) || I0 == i) &&
    //   AbLt(i, k) ==>
    //   AbSeqIndex(i, s) == AbSeqIndex(i, s');
    Seq_Props_concat_is_orig<X> ();
    // Seq_Props_concat_is_orig_param (AbAdd(k, I1), s);
    Seq_Props_concat_index_half_2nd<X> ();
    // Seq_Props_concat_index_half_2nd_param (I0, half1, AbSeqSingleton(v));
    // assert AbSeqIndex(k, half1') == v;
    
    // NOTE: explicitly assert this assertion to make postcond work
    assert forall i :: // s(k, |s|-1] keeps
      AbLt(k, i) && AbLt(i, AbSeqLen(s)) ==>
      AbSeqIndex(i, s) == AbSeqIndex(AbSub(i, AbAdd(k, I1)), half2);
    // assert forall i :: // s(k, |s|-1] keeps
    //   AbLt(k, i) &&
    //   AbLt(i, AbSeqLen(s')) ==>
    //   AbSeqIndex(i, s) == AbSeqIndex(i, s');
    AbSeqConcat(half1', half2)
  else
    Props_ltgteq ();
    Props_gt2geq ();
    // var s' := AbSeqConcat(half1, AbSeqSingleton(v));
    Seq_Props_concat_length_param (half1, AbSeqSingleton(v));
    // assert AbSeqLen(s') == len;
    Seq_Props_concat_index_half_1st<X> ();
    // assert forall i :: // s[0, k) keeps
    //   (AbLt(I0, i) || I0 == i) &&
    //   AbLt(i, k) ==>
    //   AbSeqIndex(i, s) == AbSeqIndex(i, s');
    // assert forall i :: // s(k, |s|-1] keeps
    //   AbLt(k, i) &&
    //   AbLt(i, AbSeqLen(s')) ==>
    //   AbSeqIndex(i, s) == AbSeqIndex(i, s');
    Seq_Props_concat_index_half_2nd<X> ();
    // assert AbSeqIndex(k, s') == v;
    AbSeqConcat(half1, AbSeqSingleton(v))
}

// func.requires : 0 <= i < len
function method AbSeqInit<X> (len: AbInt, func : AbInt --> X) : (s: AbSeq<X>)
  requires forall i :: (AbLt(I0, i) || I0 == i) && AbLt(i, len) ==> func.requires(i)
  ensures AbSeqLen(s) == len
  ensures forall i :: (AbLt(I0, i) || I0 == i) && AbLt(i, len) ==>
    AbSeqIndex(i, s) == func(i)
// {
//   var i : AbInt := I0;
//   var s' := AbSeqEmpty ();
//   while AbLt(i, len)
//     invariant AbLt(i, len)
//     invariant AbLt(I0, i) || I0 == i
//     invariant forall j :: (AbLt(I0, i) || I0 == i) && AbLt(i, len) ==> func.requires(i)
//   {

//   }
// }