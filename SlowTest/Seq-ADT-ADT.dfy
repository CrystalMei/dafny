type AbInt(==)
datatype Nat = Z | S(Nat)
function method adt2dt (a: AbInt) : Nat
lemma Props_adt_dt_lt (x: AbInt, y: AbInt)
  requires AbLt(x, y)
  ensures adt2dt(x) < adt2dt(y)
function method int2adt (n: int) : (AbInt)
predicate AbIsZero (n: AbInt) { n == int2adt(0) }
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
  ensures forall x :: AbLt(int2adt(0), x) || x == int2adt(0)
lemma Props_add_commutative () // x + y == y + x
  ensures forall x, y :: AbAdd(x, y) == AbAdd(y, x);
lemma Props_add_associative () // (x + y) + z == x + (y + z)
  ensures forall x, y, z :: AbAdd(AbAdd(x, y), z) == AbAdd(x, AbAdd(y, z))
lemma Props_add_identity () // x + 0 == 0 + x == x
  ensures forall x :: AbAdd(x, int2adt(0)) == x
  ensures forall x :: AbAdd(int2adt(0), x) == x
lemma Props_add_pos_is_pos () // x + Positive is Positive
  ensures forall x, a :: AbPos(a) ==> AbPos(AbAdd(x, a))
lemma Props_add_pos_is_lt () // x < x + Positive
  ensures forall x, a :: AbPos(a) ==> AbLt(x, AbAdd(x, a));
lemma Props_add_lt_is_lt () // x + a == y + b && a < b ==> x > y
  ensures forall x, y, a, b :: AbAdd(x, a) == AbAdd(y, b) ==> (AbLt(a, b) <==> AbLt(y, x))
lemma Props_add2sub () // x + y == z ==> x = z - y && y = z - x
  ensures forall x, y, z :: AbAdd(x, y) == z <==> AbSub(z, y) == x
  ensures forall x, y, z :: AbAdd(x, y) == z <==> AbSub(z, x) == y
lemma Props_gt2geq ()
  ensures forall x, y :: AbLt(x, y) <==> AbLt(AbAdd(x, int2adt(1)), y) || AbAdd(x, int2adt(1)) == y
  ensures forall x, y :: AbLt(x, y) <==> AbLt(x, AbSub(y, int2adt(1))) || x == AbSub(y, int2adt(1))

lemma Props_lt_transitive () // x < y < z
  ensures forall x, y, z :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
lemma Props_lt_addition () // a < b ==> x + a < x + b
  ensures forall x, a, b:: AbLt(a, b) ==> AbLt(AbAdd(x, a), AbAdd(x, b))

type AbSeq<X>
function method AbSeqLen (s: AbSeq<AbInt>) : AbInt
function method AbSeqIndex (i: AbInt, s: AbSeq<AbInt>) : AbInt
  requires (AbLt(int2adt(0), i) || i == int2adt(0)) && AbLt(i, AbSeqLen(s))

function method AbSeqConcat (s1: AbSeq<AbInt>, s2: AbSeq<AbInt>) : AbSeq<AbInt>
function method AbSeqIn (v: AbInt, s: AbSeq<AbInt>) : bool

function method AbSeqEmpty (): (s: AbSeq<AbInt>)
  ensures AbSeqLen(s) == int2adt(0)

function method AbSeqSingleton (i: AbInt): (s: AbSeq<AbInt>)
  ensures AbSeqLen(s) == int2adt(1)
  ensures AbLt(int2adt(0), int2adt(1)) ==> AbSeqIndex(int2adt(0), s) == i
  ensures AbSeqIn(i, s)
  ensures forall x :: x != i ==> !AbSeqIn(x, s)

function method AbSeqSlice (i: AbInt, j: AbInt, s: AbSeq<AbInt>) : (s' : AbSeq<AbInt>)
  requires AbLt(int2adt(0), i) || i == int2adt(0)
  requires AbLt(j, AbSeqLen(s)) || j == AbSeqLen(s)
  requires AbLt(i, j) || i == j
  ensures AbSeqLen(s') == AbSub(j, i)
  ensures
    // Props_lt_transitive ();
    (forall x :: AbLt(x, j) ==> AbLt(x, AbSeqLen(s))) ==>
    (forall x :: (AbLt(i, x) || i == x) ==> (AbLt(int2adt(0), x) || x == int2adt(0))) ==>
    // Props_add2sub (); Props_lt_addition ();
    (forall x, y :: AbLt(x, y) ==> AbLt(AbSub(x, i), AbSub(y, i))) ==>
    (forall x :: (AbLt(i, x) || i == x) ==> (AbLt(int2adt(0), AbSub(x, i)) || AbSub(x, i) == int2adt(0))) ==>
    forall x :: (AbLt(i, x) || i == x) && AbLt(x, j) ==> 
    AbSeqIndex(x, s) == 
    AbSeqIndex(AbSub(x, i), s') // s[i..j] w/ s[i] and w/o s[j]

lemma Seq_Props_length () // |s| >= 0
  ensures forall s: AbSeq<AbInt> :: AbSeqLen(s) == int2adt(0) || AbLt(int2adt(0), AbSeqLen(s))

lemma Seq_Props_concat_length () // |s1 + s2| == |s1| + |s2|
  ensures forall s1: AbSeq<AbInt>, s2: AbSeq<AbInt> :: AbSeqLen(AbSeqConcat(s1, s2)) == AbAdd(AbSeqLen(s1), AbSeqLen(s2))
lemma Seq_Props_concat_in () // x in s1 || x in s2 <==> x in s1 + s2
  ensures forall x: AbInt, s1: AbSeq<AbInt>, s2: AbSeq<AbInt> :: AbSeqIn(x, s1) || AbSeqIn(x, s2) <==> AbSeqIn(x, AbSeqConcat(s1, s2))
lemma Seq_Props_concat_in_sub ()
  // x in s1 ==> x in s1 + s2
  ensures forall x: AbInt, s1: AbSeq<AbInt>, s2: AbSeq<AbInt> :: AbSeqIn(x, s1) ==> AbSeqIn(x, AbSeqConcat(s1, s2))
  // x in s2 ==> x in s1 + s2
  ensures forall x: AbInt, s1: AbSeq<AbInt>, s2: AbSeq<AbInt> :: AbSeqIn(x, s2) ==> AbSeqIn(x, AbSeqConcat(s1, s2))
lemma Seq_Props_concat_in_part ()
  // x in s1 + s2 && x !in s1 ==> x in s2
  ensures forall x: AbInt, s1: AbSeq<AbInt>, s2: AbSeq<AbInt> :: AbSeqIn(x, AbSeqConcat(s1, s2)) && !AbSeqIn(x, s1) ==> AbSeqIn(x, s2)
  // x in s1 + s2 && x !in s2 ==> x in s1
  ensures forall x: AbInt, s1: AbSeq<AbInt>, s2: AbSeq<AbInt> :: AbSeqIn(x, AbSeqConcat(s1, s2)) && !AbSeqIn(x, s2) ==> AbSeqIn(x, s1)

lemma Seq_Props_index_half_1st ()
  ensures forall i: AbInt, s1: AbSeq<AbInt>, s2: AbSeq<AbInt> ::
  (AbLt(int2adt(0), i) || i == int2adt(0)) && AbLt(i, AbSeqLen(s1)) ==> // 0 <= i < |s1|
  AbLt(i, AbSeqLen(AbSeqConcat(s1, s2))) ==> // i < |s1| < |s1 + s2|
  AbSeqIndex(i, s1) == AbSeqIndex(i, AbSeqConcat(s1, s2))

lemma Seq_Props_index_half_2nd ()
  ensures forall i: AbInt, s1: AbSeq<AbInt>, s2: AbSeq<AbInt> ::
  (AbLt(int2adt(0), i) || i == int2adt(0)) && AbLt(i, AbSeqLen(s2)) ==> // 0 <= i < |s2|
  AbLt(i, AbSeqLen(AbSeqConcat(s1, s2))) ==> // i < |s2| < |s1 + s2|
  AbAdd(AbSeqIndex(i, s2), AbSeqLen(s1)) == AbSeqIndex(i, AbSeqConcat(s1, s2))

lemma Seq_Props_in_empty () // empty seq
  ensures forall x: AbInt, s: AbSeq<AbInt> :: AbSeqLen(s) == int2adt(0) ==> !AbSeqIn(x, s)
lemma Seq_Props_in_non_empty () // i in s ==> |s| > 0
  ensures forall i: AbInt, s: AbSeq<AbInt> :: AbSeqIn(i, s) ==> AbLt(int2adt(0), AbSeqLen(s))

method AbSeqRemove (v: AbInt, s: AbSeq<AbInt>) returns (s': AbSeq<AbInt>)
  requires AbSeqIn(v, s)
  ensures forall x :: x != v ==> AbSeqIn(x, s) ==> AbSeqIn(x, s')
  ensures AbSeqLen(s) == AbAdd(AbSeqLen(s'), int2adt(1))
{
  Props_add_identity ();
  s' := RemoveHelper(v, AbSeqEmpty(), s, AbSeqLen(s));
}

method RemoveHelper (v: AbInt, head: AbSeq<AbInt>, tail: AbSeq<AbInt>, len: AbInt) returns (r: AbSeq<AbInt>)
  requires AbSeqIn(v, tail)
  requires len == AbSeqLen(tail)
  ensures forall x :: x != v ==> (AbSeqIn(x, head) || AbSeqIn(x, tail) ==> AbSeqIn(x, r))
  ensures AbAdd(AbSeqLen(head), AbSeqLen(tail)) == AbAdd(AbSeqLen(r), int2adt(1)) // length
  decreases adt2dt(len)
{

  /* Properties for ITE */
  Props_add_associative ();
  Props_int_pos(1);
  Props_all_nonneg ();
  Props_add_pos_is_lt ();
  Seq_Props_in_non_empty ();
  Seq_Props_concat_length ();
  Seq_Props_concat_in_sub ();
  Seq_Props_concat_in_part ();

  Props_add_identity ();
  // assert AbAdd(int2adt(0), int2adt(1)) == int2adt(1);
  // Props_inc2dec ();
  // Props_gt2geq ();
  // assert AbLt(int2adt(0), int2adt(1));
  // assert AbLt(int2adt(0), AbSeqLen(tail));
  // assert AbLt(int2adt(1), AbSeqLen(tail)) || int2adt(1) == AbSeqLen(tail);

  // Props_lt_transitive ();
  // Props_add2sub (); Props_lt_addition ();
  // assert (forall x :: (AbLt(int2adt(1), x) || int2adt(1) == x) ==> (AbLt(int2adt(0), AbSub(x, int2adt(1))) || AbSub(x, int2adt(1)) == int2adt(0)));

  // var tail' := AbSeqSlice(int2adt(1), AbSeqLen(tail), tail);
  var tail' := AbSeqCutHead(tail);
  if AbSeqIndex(int2adt(0), tail) == v {
    r := AbSeqConcat(head, tail');
  } else {
    Props_adt_dt_lt (AbSeqLen(tail'), AbSeqLen(tail));
    Seq_Props_concat_in ();
    var tail_hd := AbSeqSingleton(AbSeqIndex(int2adt(0), tail));
    var head' := AbSeqConcat(head, tail_hd);
    r := RemoveHelper(v, head', tail', AbSeqLen(tail'));
  }
}

// method AbSeqRemoveIdx (i: AbInt, s: AbSeq<AbInt>) returns (s': AbSeq<AbInt>)
//   requires 
//     (AbLt(int2adt(0), i) || i == int2adt(0)) && AbLt(i, AbSeqLen(s))
//   ensures AbSeqLen(s) == AbInc(AbSeqLen(s'))
//   ensures forall x :: (AbLt(int2adt(0), x) || x == int2adt(0)) && AbLt(x, i) ==> AbSeqIndex(x, s') == AbSeqIndex(x, s)
//   ensures forall x :: (AbLt(i, x) || i == x) && AbLt(x, AbSeqLen(s')) ==> AbSeqIndex(x, s') == AbSeqIndex(AbInc(x), s)
// {
//   Props_add0 ();
//   s' := RemoveIdxHelper(i, AbSeqEmpty(), s, AbSeqLen(s));
// }

// method RemoveIdxHelper (i: AbInt, head: AbSeq<AbInt>, tail: AbSeq<AbInt>, len: AbInt) returns (r: AbSeq<AbInt>)
//   requires AbLt(int2adt(0), AbSeqLen(tail))
//   requires var i' := AbSub(i, AbSeqLen(head)); // i' = i - |head|
//     (AbLt(int2adt(0), i') || i' == int2adt(0)) && AbLt(i', AbSeqLen(tail))
//   requires len == AbSeqLen(tail)
//   ensures
//     AbLt(AbSeqLen(head), AbSeqLen(r)) ==>
//     (forall x, y, z :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)) ==>
//     forall x :: (AbLt(int2adt(0), x) || x == int2adt(0)) && AbLt(x, AbSeqLen(head)) ==>
//     AbSeqIndex(x, r) == AbSeqIndex(x, head) // head keeps
//   ensures
//     forall x :: (AbLt(int2adt(0), x) || x == int2adt(0)) && AbLt(x, AbSeqLen(tail)) ==>
//     AbSeqIndex(x, r) == AbSeqIndex(x, tail) // head keeps
//   ensures AbAdd(AbSeqLen(head), AbSeqLen(tail)) == AbInc(AbSeqLen(r)) // length
//   decreases adt2dt(len)
// {
//   /* Properties for ITE */
//   Props_add_associative ();
//   Props_inc_is_add1 ();
//   Seq_Props_in_non_empty ();
//   Seq_Props_concat_length ();
//   Seq_Props_concat_in_sub ();
//   Seq_Props_concat_in_part ();

//   if i == int2adt(0) {
//     var tail' := AbSeqCutHead(tail);
//     r := AbSeqConcat(head, tail');
//   } else {
//     var tail' := AbSeqCutHead(tail);
//     Props_int_pos(1);
//     Props_add_pos_is_lt ();
//     Props_adt_dt_lt (AbSeqLen(tail'), AbSeqLen(tail));
//     Seq_Props_concat_in ();
//     var tail_hd := AbSeqSingleton(AbSeqIndex(int2adt(0), tail));
//     var head' := AbSeqConcat(head, tail_hd);
//     r := RemoveIdxHelper(i, head', tail', AbSeqLen(tail'));
//   }
// }

// method AbSeqUpdate (i: AbInt, v: AbInt, s: AbSeq<AbInt>) returns (s': AbSeq<AbInt>)
//   requires (AbLt(int2adt(0), i) || i == int2adt(0)) && AbLt(i, AbSeqLen(s))
//   ensures AbSeqLen(s) == AbSeqLen(s')
//   ensures AbSeqIndex(i, s') == v
// {
  
// }

method AbSeqCutHead (s: AbSeq<AbInt>) returns (s': AbSeq<AbInt>)
  requires AbLt(int2adt(0), AbSeqLen(s)) // |s| > 0
  ensures AbSeqLen(s) == AbAdd(AbSeqLen(s'), int2adt(1))
  ensures forall x :: AbSeqIn(x, s') ==> AbSeqIn(x, s)
  ensures s == AbSeqConcat(AbSeqSingleton(AbSeqIndex(int2adt(0), s)), s')
  ensures // need to match precond for Seq_index
    (forall x :: AbLt(int2adt(0), AbAdd(x, int2adt(1)))) ==> // 0 < x + 1
    (forall x :: AbLt(x, AbSeqLen(s')) ==> AbLt(AbAdd(x, int2adt(1)), AbSeqLen(s))) ==> // x + 1 < |s|
    forall x :: // 0 <= x < |s'|
    (AbLt(int2adt(0), x) || x == int2adt(0)) &&
    (AbLt(x, AbSeqLen(s'))) ==>
    AbSeqIndex(AbAdd(x, int2adt(1)), s) == 
    AbSeqIndex(x, s') // s[x + 1] == s'[x]
// {
//   s' := AbSeqEmpty ();
//   var i := int2adt(0);
//     Props_inc2dec ();
//     assert AbInc(AbDec(AbSeqLen(s))) == AbSeqLen(s);
//     Props_inc_is_add1 (); 
//     Props_lt_addition (); // i + 1 < |s|
//     Props_add_commutative ();
//     assert AbLt(i, AbDec(AbSeqLen(s))) ==> AbLt(AbAdd(i, int2adt(1)), AbAdd(AbDec(AbSeqLen(s)), int2adt(1)));
//     assert AbLt(AbAdd(i, int2adt(1)), AbAdd(AbDec(AbSeqLen(s)), int2adt(1))) ==> AbLt(AbInc(i), AbSeqLen(s));
//   while AbLt(i, AbDec(AbSeqLen(s)))
//     decreases adt2dt(AbSub(AbSeqLen(s), i))
//   {
//     Props_all_nonneg ();
//     Props_int_pos(1);
//     Props_inc_is_add1 (); 
//     Props_add_pos_is_lt (); // 0 <= i + 1

//     Props_add2sub ();
//     Props_add_lt_is_lt ();
//     Props_add_commutative ();
//     Props_adt_dt_lt(AbSub(AbSeqLen(s), AbInc(i)), AbSub(AbSeqLen(s), i)); // decreases

//     Props_inc2dec ();
//     Props_lt_addition (); // i + 1 < |s|
//     assert AbLt(AbInc(i), AbSeqLen(s));
//     i := AbInc(i); // no head

//     s' := AbSeqConcat(s', AbSeqSingleton(AbSeqIndex(i, s)));
//   }

//   Seq_Props_concat_length ();
//   assert forall x :: AbSeqIn(x, s') ==> AbSeqIn(x, s);


//   // Props_all_nonneg ();
//   // Props_int_pos(1);
//   // Props_gt2geq ();
//   // Props_inc_is_add1 (); Props_inc2dec ();
//   // Props_add_pos_is_pos (); Props_add_pos_is_lt ();
//   // Props_lt_transitive (); Props_add_commutative ();
//   // assert forall x :: (AbLt(int2adt(0), x) || x == int2adt(0));
//   // assert forall x :: (AbLt(int2adt(0), AbInc(x)) || AbInc(x) == int2adt(0));
//   // assert forall x :: AbLt(x, AbSeqLen(s')) ==> AbLt(AbInc(x), AbSeqLen(s));

// }