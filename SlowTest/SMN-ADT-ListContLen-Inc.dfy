// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<X> = Nil | Cons(head: X, tail: List<X>)
datatype Nat = Z | S(Nat)

type AbInt(==)
function method int2adt (n: int) : (AbInt)
function method adt2dt (a: AbInt) : Nat
lemma Props_adt_dt_lt (x: AbInt, y: AbInt)
  requires AbLt(x, y)
  ensures adt2dt(x) < adt2dt(y)

predicate AbIsZero (n: AbInt) { n == int2adt(0) }
predicate AbPos (n: AbInt) { !AbIsZero(n) }
// predicate AbNonNeg (n: AbInt) { true }

function method AbLt(n: AbInt, m: AbInt) : bool
function method AbInc1(n: AbInt): (r: AbInt)
function method AbInc(n: AbInt, m: AbInt) : (r: AbInt)
function method AbDec(n: AbInt, m: AbInt) : (r: AbInt)
function method AbDiv2(n: AbInt): (r: AbInt)
  ensures AbLt(AbInc(r, r), n) || AbInc(r, r) == n
function method AbSetLen(s: set<AbInt>) : (l: AbInt)
lemma SetLen_Props()
  ensures forall x :: AbSetLen(x) == int2adt(0) <==> x == {}
  ensures forall x: AbInt :: AbSetLen({x}) == int2adt(1)
  ensures forall x: AbInt, A: set<AbInt> :: x in A ==> AbSetLen(A) == AbInc1(AbSetLen(A - {x}))

// Set generation: lo <= x < lo+len
// experiment with more trigger options
function method AbBoundSet(lo: AbInt, len: AbInt): (S: set<AbInt>)
  ensures AbSetLen(S) == len
  ensures forall x :: (AbLt(lo, x) || lo == x) && AbLt(x, AbInc(lo, len)) <==> x in S
  // Try not to assign every element with AbAdd()
  // ensures S == set x | 0 <= x < len :: AbAdd(lo, int2adt(x))

/* Properties */
lemma Props_int_pos(a: int)
  ensures AbPos(int2adt(a))
lemma Props_all_nonneg ()
  ensures forall x :: AbLt(int2adt(0), x) || x == int2adt(0)
lemma Props_one_in_bound ()
  ensures forall a, x :: (AbLt(a, x) || a == x) && (AbLt(x, AbInc1(a))) ==> a == x
lemma Props_inc_one ()
  ensures forall x :: AbInc1(x) == AbInc(x, int2adt(1)) == AbInc(int2adt(1), x)
lemma Props_inc_zero ()
  ensures forall x :: AbInc(x, int2adt(0)) == AbInc(int2adt(0), x) == x
lemma Props_1inc1_is_2 ()
  ensures AbInc1(int2adt(1)) == int2adt(2)
lemma Props_lt2gteq () // x < y <==> !x > y && x != y
  ensures forall x, y :: AbLt(x, y) <==> !(AbLt(y, x) || x == y)
lemma Props_inc2dec ()
  ensures forall x, y, z :: AbInc(x, y) == z ==> AbDec(z, x) == y && AbDec(z, y) == x
lemma Props_gt0_is_geq1 ()
  ensures forall x :: AbLt(int2adt(0), x) <==> AbLt(int2adt(1), x) || x == int2adt(1)
// lemma Props_gt0_is_geq1_param (x: AbInt)
//   ensures AbLt(int2adt(0), x) <==> AbLt(int2adt(1), x) || x == int2adt(1)

lemma Props_lt_addition () // a < b ==> x + a < x + b
  ensures forall x, a, b:: AbLt(a, b) ==> AbLt(AbInc(x, a), AbInc(x, b))
lemma Props_lt_transitive () // x < y < z
  ensures forall x, y, z :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
lemma Props_lt_inc_is_lt () // x + a < y ==> x < y
  ensures forall x, y, a :: AbLt(AbInc(x, a), y) ==> AbLt(x, y)

// lemma Props_inc_commutative () // x + y == y + x
//   ensures forall x, y :: AbInc(x, y) == AbInc(y, x);
lemma Props_inc_associative () // (x + y) + z == x + (y + z)
  ensures forall x, y, z :: AbInc(AbInc(x, y), z) == AbInc(x, AbInc(y, z))
lemma Props_inc_addition () // x + a == y + a ==> x == y
  ensures forall x, y, a :: AbInc(x, a) == AbInc(y, a) <==> x == y
lemma Props_inc_pos_is_pos () // x + Positive is Positive
  ensures forall x, y :: AbPos(y) ==> AbPos(AbInc(x, y))
  ensures forall x, y :: AbPos(y) ==> AbPos(AbInc(y, x))
lemma Props_inc_pos_is_lt () // x < x + Positive
  ensures forall x, y :: AbPos(y) ==> AbLt(x, AbInc(x, y))
  ensures forall x, y :: AbPos(y) ==> AbLt(x, AbInc(y, x))
lemma Props_inc_lt_is_lt () // x = y + a && a < b ==> x < y + b
  ensures forall x, y, a, b :: (x == AbInc(y, a)) && AbLt(a, b) ==> AbLt(x, AbInc(y, b))
// Some instantiation
lemma Props_inc_lt_is_lt_param (x: AbInt, y: AbInt, a: AbInt, b: AbInt)
  ensures (x == AbInc(y, a)) && AbLt(a, b) ==> AbLt(x, AbInc(y, b))

lemma Props_inc_dec_is_inc () // x + j + (i - j) == x + i
    ensures forall x, i, j :: AbInc(AbInc(x, j), AbDec(i, j)) == AbInc(x, i) // trigger may loop
// Some instantiation
lemma Props_inc_dec_is_inc_param(x: AbInt, i: AbInt, j: AbInt)
  ensures AbInc(AbInc(x, j), AbDec(i, j)) == AbInc(x, i)

lemma Props_div_pos () // x > 1 ==> x/2 is Positive
  ensures forall x :: AbLt(int2adt(1), x) ==> AbPos(AbDiv2(x))
lemma Props_div_inc1_is_leq () // 1 <= x ==> (x+1)/2 <= x
  ensures forall x :: AbLt(int2adt(1), x) || x == int2adt(1) ==> AbLt(AbDiv2(AbInc1(x)), x) || AbDiv2(AbInc1(x)) == x
lemma Props_div_inc1_is_leq_param (x: AbInt)
  ensures AbLt(int2adt(1), x) || x == int2adt(1) ==> AbLt(AbDiv2(AbInc1(x)), x) || AbDiv2(AbInc1(x)) == x
lemma Props_div_and_inc1_is_leq () // 1 <= x ==> x/2+1 <= x
  ensures forall x :: AbLt(int2adt(1), x) || x == int2adt(1) ==> AbLt(AbInc1(AbDiv2(x)), x) || AbInc1(AbDiv2(x)) == x
lemma Props_div_and_inc1_is_leq_param (x: AbInt)
  ensures AbLt(int2adt(1), x) || x == int2adt(1) ==> AbLt(AbInc1(AbDiv2(x)), x) || AbInc1(AbDiv2(x)) == x

function method Length(xs: List<AbInt>): AbInt
{
  match xs
  case Nil => int2adt(0)
  case Cons(_, tail) => AbInc1(Length(tail))
}
 
function method Split(xs: List<AbInt>, b: AbInt): (List<AbInt>, List<AbInt>)
  ensures var r := Split(xs, b); Length(xs) == AbInc(Length(r.0), Length(r.1))
  decreases xs
{
  Props_inc_associative ();
  Props_inc_zero (); Props_inc_one ();  
  match xs
  case Nil => (Nil, Nil)
  case Cons(x, tail) =>
    var (L, R) := Split(tail, b);
    if AbLt(x, b) then
      (Cons(x, L), R)
    else
      (L, Cons(x, R))
}

lemma Split_Correct(xs: List<AbInt>, b: AbInt)
  requires NoDuplicates(xs)
  ensures var r := Split(xs, b);
    Elements(r.0) == (set x | x in Elements(xs) && AbLt(x, b)) && // x < b
    Elements(r.1) == (set x | x in Elements(xs) && !AbLt(x, b)) && // b <= x
    NoDuplicates(r.0) && NoDuplicates(r.1)
{
  match xs
  case Nil =>
  case Cons(_, tail) =>
    Split_Correct(tail, b);
}

function Elements(xs: List<AbInt>): set<AbInt>
{
  match xs
  case Nil => {}
  case Cons(x, tail) => {x} + Elements(tail)
}

lemma Elements_Property(xs: List<AbInt>)
  requires NoDuplicates(xs)
  ensures AbSetLen(Elements(xs)) == Length(xs)
{
  SetLen_Props();
  // Props_add_commutative ();
  Props_inc_associative ();
}

predicate NoDuplicates(xs: List<AbInt>)
{
  match xs
  case Nil => true
  case Cons(x, tail) =>
    x !in Elements(tail) && NoDuplicates(tail)
}

// standard theorems and their proofs

lemma Cardinality(A: set<AbInt>, B: set<AbInt>)
  requires A <= B
  ensures AbLt(AbSetLen(A), AbSetLen(B)) || AbSetLen(A) == AbSetLen(B)
{
  SetLen_Props ();
  Props_all_nonneg ();
  Props_inc_addition ();
  Props_lt_addition ();
  Props_inc_zero (); Props_inc_one ();
  if A != {} {
    var x :| x in A;
    Cardinality(A - {x}, B - {x});
  }
}

lemma SetEquality(A: set<AbInt>, B: set<AbInt>)
  requires A <= B && AbSetLen(A) == AbSetLen(B)
  ensures A == B
{
  SetLen_Props ();
  Props_inc_addition ();
  Props_inc_zero (); Props_inc_one ();
  if A == {} {
  } else {
    var x :| x in A;
    SetEquality(A - {x}, B - {x});
  }
}

function IntRange(lo: AbInt, len: AbInt): set<AbInt>
  ensures AbSetLen(IntRange(lo, len)) == len
{
  var S := AbBoundSet(lo, len);
  // Try not to assign every element with AbAdd()
  // assert len != 0 ==> S == IntRange(lo, len - 1) + {AbAdd(lo, int2adt(len - 1))};
  assert forall x :: ((AbLt(lo, x) || lo == x) && AbLt(x, AbInc(lo, len))) ==> x in S;
  S
}

function method SmallestMissingNumber(xs: List<AbInt>): AbInt
{
  SMN(xs, int2adt(0), Length(xs))
}

function method SMN(xs: List<AbInt>, n: AbInt, len: AbInt): AbInt
  requires len == Length(xs)
  decreases adt2dt(len)
{
  if AbLt(int2adt(2), len) || int2adt(2) == len then
    var (L, R) := Split(xs, AbInc(n, AbDiv2(len)));
    var llen := Length(L);

    /* Props for ITE */
    Props_lt_transitive (); // 0 < len
    Props_lt2gteq ();

    if AbLt(llen, AbDiv2(len)) then
      Props_int_pos(2); // 0 < 2
      Props_lt_inc_is_lt (); // x + a < y ==> x < y
      Props_adt_dt_lt (llen, len); // decreases (pre: llen < len/2 < len)
      SMN(L, n, llen)
    else
      Props_all_nonneg ();
      Props_int_pos(1);
      Props_1inc1_is_2 ();
      Props_inc_one (); // 1 < 2
      Props_inc_pos_is_lt ();
      Props_div_pos (); // 1 <= len/2
      Props_inc2dec ();
      Props_adt_dt_lt (AbDec(len, llen), len);
      SMN(R, AbInc(n, llen), AbDec(len, llen))
  else if xs.Cons? then
    if xs.head == n then AbInc1(n) else n
  else
    n
}

// proof of lemmas supporting proof of main theorem

lemma SmallestMissingNumber_Correct(xs: List<AbInt>)
  requires NoDuplicates(xs)
  ensures var s := SmallestMissingNumber(xs);
    s !in Elements(xs) &&
    forall x :: (AbLt(int2adt(0), x) || int2adt(0) == x) && AbLt(x, s) ==> x in Elements(xs)
{
  Props_all_nonneg ();
  SMN_Correct(xs, int2adt(0), Length(xs));
}

// element, len, index -> abstract type
lemma SMN_Correct(xs: List<AbInt>, n: AbInt, len: AbInt)
  requires NoDuplicates(xs)
  requires forall x :: x in Elements(xs) ==> (AbLt(n, x) || n == x)
  requires len == Length(xs)
  ensures var s := SMN(xs, n, len);
    (AbLt(n, s) || n == s) &&
    (AbLt(s, AbInc(n, len)) || s == AbInc(n, len)) &&
    s !in Elements(xs) &&
    forall x :: (AbLt(n, x) || n == x) && AbLt(x, s) ==> x in Elements(xs)
  decreases adt2dt(len)
{
  if AbLt(int2adt(2), len) || int2adt(2) == len {
    var (L, R) := Split(xs, AbInc(n, AbDiv2(len)));
    Split_Correct(xs, AbInc(n, AbDiv2(len)));
    var llen := Length(L);
    Elements_Property(L);  // NoDuplicates property
    var bound := IntRange(n, AbDiv2(len));
    Cardinality(Elements(L), bound);

    /* Props for ITE */
    Props_lt_transitive (); // 0 < len
    Props_lt2gteq ();

    if AbLt(llen, AbDiv2(len)) {
      var s := SMN(L, n, llen);
      Props_int_pos(2); // 0 < 2
      Props_lt_inc_is_lt (); // x + a < y ==> x < y
      Props_adt_dt_lt (llen, len);
      SMN_Correct(L, n, llen);

      /* map boundary */
      Props_lt_addition (); // a < b ==> x + a < x + b: Lt(s, n+llen) ==> Lt(s, n+len)
      // Props_inc_lt_is_lt (); // x = y + a && a < b ==> x < y + b: s==n+llen ==> Lt(s, n+len)
      Props_inc_lt_is_lt_param(s, n, llen, len); // no trigger loop
    }
    
    else {
      Props_all_nonneg ();
      Props_inc2dec ();
      var s := SMN(R, AbInc(n, llen), AbDec(len, llen));
      Props_int_pos(1);
      Props_1inc1_is_2 ();
      Props_inc_one (); // 1 < 2
      Props_inc_pos_is_lt ();
      Props_div_pos (); // 1 <= len/2
      Props_adt_dt_lt (AbDec(len, llen), len);
      SMN_Correct(R, AbInc(n, llen), AbDec(len, llen));

      /* map boundary */
      // Props_inc_dec_is_inc();
      Props_inc_dec_is_inc_param(n, len, llen); // no trigger loop
      forall x | (AbLt(n, x) || n == x) && AbLt(x, s)
        ensures x in Elements(xs)
      {
        if AbLt(x, AbInc(n, llen)) {
          SetEquality(Elements(L), bound);
        }
      }
    }
  } 
  else {
    Props_inc_one (); Props_inc_zero (); // n + 1
    Props_int_pos(1); // 0 < 1
    Props_all_nonneg ();
    Props_lt2gteq (); // len < 2
    Props_1inc1_is_2 ();
    Props_inc_pos_is_lt ();
    Props_one_in_bound ();
  }
}

function method SMN'(xs: List<AbInt>, n: AbInt, len: AbInt): AbInt
  requires len == Length(xs)
  decreases adt2dt(len)
{
  if xs == Nil then n
  else
    var half := AbDiv2(AbInc1(len)); // half = (len+1)/2
    var (L, R) := Split(xs, AbInc(n, half));
    var llen := Length(L);

    /* Props for ITE */
    Props_int_pos(1); // 0 < 1
    Props_inc_one (); Props_inc_zero ();
    Props_inc_pos_is_lt (); // x < x + Positive
    Props_lt_transitive (); // len >= 1

    if AbLt(llen, half) then
      Props_gt0_is_geq1 (); // x > 0 ==> x >= 1
      Props_div_inc1_is_leq_param (len); // (x+1)/2 <= x
      Props_adt_dt_lt (llen, len);
      SMN'(L, n, llen)
    else
      Props_all_nonneg ();
      Props_lt2gteq ();
      Props_div_pos ();
      Props_inc2dec (); // llen is Positive
      Props_adt_dt_lt (AbDec(len, llen), len);
      SMN'(R, AbInc(n, llen), AbDec(len, llen))
}

lemma SMN'_Correct(xs: List<AbInt>, n: AbInt, len: AbInt)
  requires NoDuplicates(xs)
  requires forall x :: x in Elements(xs) ==> (AbLt(n, x) || n == x)
  requires len == Length(xs)
  ensures var s := SMN'(xs, n, len);
    (AbLt(n, s) || n == s) &&
    (AbLt(s, AbInc(n, len)) || s == AbInc(n, len)) &&
    s !in Elements(xs) &&
    forall x :: (AbLt(n, x) || n == x) && AbLt(x, s) ==> x in Elements(xs)
  decreases adt2dt(len)
{
  if xs == Nil {
    Props_inc_zero ();
    Props_lt2gteq ();
  } 
  else {
    var half := AbDiv2(AbInc1(len)); // half = (len+1)/2
    var (L, R) := Split(xs, AbInc(n, half));
    Split_Correct(xs, AbInc(n, half));
    var llen := Length(L);
    Elements_Property(L);  // use the NoDuplicates property
    var bound := IntRange(n, half);
    Cardinality(Elements(L), bound);
    
    /* Props for ITE */
    Props_int_pos(1); // 0 < 1
    Props_inc_one (); Props_inc_zero ();
    Props_inc_pos_is_lt (); // x < x + Positive
    Props_lt_transitive (); // len >= 1

    if AbLt(llen, half) {
      var s := SMN'(L, n, llen);
      Props_gt0_is_geq1 (); // x > 0 ==> x >= 1
      Props_div_inc1_is_leq_param (len);  // no trigger loop
      Props_adt_dt_lt (llen, len);
      SMN'_Correct(L, n, llen);

      /* map boundary */
      Props_lt_addition ();
      Props_inc_lt_is_lt_param(s, n, llen, len); // no trigger loop
    }
    
    else {
      Props_all_nonneg ();
      Props_lt2gteq ();
      Props_div_pos ();
      Props_inc2dec (); // llen is Positive
      var s := SMN'(R, AbInc(n, llen), AbDec(len, llen));
      Props_adt_dt_lt (AbDec(len, llen), len);
      SMN'_Correct(R, AbInc(n, llen), AbDec(len, llen));

      /* map boundary */
      Props_inc_dec_is_inc_param(n, len, llen); // no trigger loop
      forall x | (AbLt(n, x) || n == x) && AbLt(x, s)
        ensures x in Elements(xs)
      {
        if AbLt(x, AbInc(n, llen)) {
          SetEquality(Elements(L), bound);
        }
      }
    }
  }
}

function method SMN''(xs: List<AbInt>, n: AbInt, len: AbInt): AbInt
  requires len == Length(xs)
  decreases adt2dt(len)
{
  if xs == Nil then n
  else
    var half := AbInc1(AbDiv2(len)); // half = len/2 + 1
    var (L, R) := Split(xs, AbInc(n, half));
    var llen := Length(L);

    /* Props for ITE */
    Props_int_pos (1); // 0 < 1
    Props_inc_one (); Props_inc_zero ();
    Props_inc_pos_is_lt (); // x < x + Positive
    Props_lt_transitive ();

    if AbLt(llen, half) then
      Props_gt0_is_geq1 (); // x > 0 ==> x >= 1
      Props_div_and_inc1_is_leq_param (len); // x/2+1 <= x
      Props_adt_dt_lt (llen, len);
      SMN''(L, n, llen)
    else
      Props_all_nonneg ();
      Props_lt2gteq (); // llen >= len/2 + 1
      Props_inc_pos_is_pos (); // 0 < x + 1
      Props_inc2dec ();
      Props_adt_dt_lt (AbDec(len, llen), len);
      SMN''(R, AbInc(n, llen), AbDec(len, llen))
}

lemma SMN''_Correct(xs: List<AbInt>, n: AbInt, len: AbInt)
  requires NoDuplicates(xs)
  requires forall x :: x in Elements(xs) ==> (AbLt(n, x) || n == x)
  requires len == Length(xs)
  ensures var s := SMN''(xs, n, len);
    (AbLt(n, s) || n == s) &&
    (AbLt(s, AbInc(n, len)) || s == AbInc(n, len)) &&
    s !in Elements(xs) &&
    forall x :: (AbLt(n, x) || n == x) && AbLt(x, s) ==> x in Elements(xs)
  decreases adt2dt(len)
{
  if xs == Nil {
    Props_inc_zero ();
    Props_lt2gteq ();
  } 
  else {
    var half := AbInc1(AbDiv2(len)); // half = len/2 + 1
    var (L, R) := Split(xs, AbInc(n, half));
    Split_Correct(xs, AbInc(n, half));
    var llen := Length(L);
    Elements_Property(L);  // use the NoDuplicates property
    var bound := IntRange(n, half);
    Cardinality(Elements(L), bound);

    /* Props for ITE */
    Props_int_pos (1); // 0 < 1
    Props_inc_one (); Props_inc_zero ();
    Props_inc_pos_is_lt (); // x < x + Positive
    Props_lt_transitive ();

    if AbLt(llen, half) {
      var s := SMN''(L, n, llen);
      Props_gt0_is_geq1 (); // x > 0 ==> x >= 1
      Props_div_and_inc1_is_leq_param (len); // x/2+1 <= x
      Props_adt_dt_lt (llen, len);
      SMN''_Correct(L, n, llen);

      /* map boundary */
      Props_lt_addition ();
      Props_inc_lt_is_lt_param(s, n, llen, len); // no trigger loop
    } else {
      Props_all_nonneg ();
      Props_lt2gteq (); // llen >= len/2 + 1
      Props_inc_pos_is_pos (); // 0 < x + 1
      Props_inc2dec ();
      Props_adt_dt_lt (AbDec(len, llen), len);
      var s := SMN''(R, AbInc(n, llen), AbDec(len, llen));
      SMN''_Correct(R, AbInc(n, llen), AbDec(len, llen));

      /* map boundary */
      Props_inc_dec_is_inc_param(n, len, llen); // no trigger loop
      forall x | (AbLt(n, x) || n == x) && AbLt(x, s)
        ensures x in Elements(xs)
      {
        if AbLt(x, AbInc(n, llen)) {
          SetEquality(Elements(L), bound);
        }
      }
    }
  }
}

// // TODO: need more concrete props to make it verified.
// method Main() {
//   var xs := Nil;
//   assert Length(xs) == int2adt(0);
//   var s := SmallestMissingNumber(xs);
//   Props_all_nonneg ();
//   Props_inc_associative ();
//   Props_add_identity ();
//   Props_add_commutative ();
//   Props_inc_pos ();
//   Props_int_pos(2);
//   Props_lt_transitive ();
//   Props_lt2gteq ();
//   assert s == int2adt(0);
//   print s, " ";  // 0
//   var a := Cons(int2adt(2), Cons(int2adt(0), Nil));
//   Props_two_is_one_plus_one ();
//   assume int2adt(1) == AbDiv2(int2adt(2));
//   assume AbLt(int2adt(0), int2adt(1));
//   assume AbLt(int2adt(1), int2adt(2));
//   // assert SmallestMissingNumbxer(a) == int2adt(1);
//   // print SmallestMissingNumber(a), " ";  // 1
//   a := Cons(int2adt(3), Cons(int2adt(1), a));
//   // assert SmallestMissingNumber(a) == int2adt(4);
// //   print SmallestMissingNumber(a), " ";  // 4
//   a := Cons(int2adt(7), Cons(int2adt(4), Cons(int2adt(6), a)));
//   // assert SmallestMissingNumber(a) == int2adt(5);
// //   print SmallestMissingNumber(a), "\n";  // 5
// }
