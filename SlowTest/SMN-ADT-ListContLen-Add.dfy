// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<X> = Nil | Cons(head: X, tail: List<X>)

type AbInt(==)
datatype Nat = Z | S(Nat)
function method int2adt (n: int) : (AbInt)
function method adt2dt (a: AbInt) : Nat
lemma Props_adt_dt_lt (x: AbInt, y: AbInt)
  requires AbLt(x, y)
  ensures adt2dt(x) < adt2dt(y)

predicate AbIsZero (n: AbInt) { n == int2adt(0) }
predicate AbPos (n: AbInt) { !AbIsZero(n) }
// predicate AbNonNeg (n: AbInt) { true }

function method AbLt(n: AbInt, m: AbInt) : bool
function method AbAdd(n: AbInt, m: AbInt) : (r: AbInt)
function method AbSub(n: AbInt, m: AbInt) : (r: AbInt)
function method AbDiv2(n: AbInt): (r: AbInt)
  ensures AbLt(AbAdd(r, r), n) || AbAdd(r, r) == n
function method AbSetLen(s: set<AbInt>) : (l: AbInt)
lemma SetLen_Props()
  ensures forall x :: AbSetLen(x) == int2adt(0) <==> x == {}
  ensures forall x: AbInt :: AbSetLen({x}) == int2adt(1)
  ensures forall x: AbInt, A: set<AbInt> :: x in A ==> AbSetLen(A) == AbAdd(AbSetLen(A - {x}), int2adt(1))
  
  // ensures forall x: AbInt, A, B: set<AbInt> :: x in A && x in B ==> 
  // ensures forall A: set<AbInt>, B : set<AbInt> :: AbAdd(AbSetLen(A+B), AbSetLen(A*B)) == AbAdd(AbSetLen(A), AbSetLen(B))
  // ensures forall A: set<AbInt>, B : set<AbInt> :: AbAdd(AbSetLen(A-B), AbSetLen(A*B)) == AbSetLen(A)
  // ensures forall A: set<AbInt>, B : set<AbInt> :: A !! B ==> AbSetLen(A+B) == AbAdd(AbSetLen(A), AbSetLen(B))
  // ensures forall A: set<AbInt>, B : set<AbInt> :: AbLt(AbSetLen(A+B), AbAdd(AbSetLen(A), AbSetLen(B))) || AbSetLen(A+B) == AbAdd(AbSetLen(A), AbSetLen(B))

// Set generation: lo <= x < lo+len
// experiment with more trigger options
function method AbBoundSet(lo: AbInt, len: AbInt): (S: set<AbInt>)
  ensures AbSetLen(S) == len
  ensures forall x :: (AbLt(lo, x) || lo == x) && AbLt(x, AbAdd(lo, len)) <==> x in S
  // Try not to assign every element with AbAdd()
  // ensures S == set x | 0 <= x < len :: AbAdd(lo, int2adt(x))

/* Properties */
lemma Props_int_pos(a: int)
  ensures AbPos(int2adt(a))

lemma Props_all_nonneg ()
  ensures forall x :: AbLt(int2adt(0), x) || x == int2adt(0)
lemma Props_one_in_bound ()
  ensures forall a, x :: (AbLt(a, x) || a == x) && (AbLt(x, AbAdd(a, int2adt(1)))) ==> a == x
lemma Props_2is1add1 ()
  ensures int2adt(2) == AbAdd(int2adt(1), int2adt(1))
lemma Props_gt0_geq1 ()
  ensures forall x :: AbLt(int2adt(0), x) <==> AbLt(int2adt(1), x) || x == int2adt(1)
lemma Props_gt0_geq1_param (x: AbInt)
  ensures AbLt(int2adt(0), x) <==> AbLt(int2adt(1), x) || x == int2adt(1)

lemma Props_lt_is_not_geq () // x < y <==> !x > y && x != y
  ensures forall x, y :: AbLt(x, y) <==> !(AbLt(y, x) || x == y)
lemma Props_lt_addition () // a < b ==> x + a < x + b
  ensures forall x, a, b:: AbLt(a, b) ==> AbLt(AbAdd(x, a), AbAdd(x, b))
lemma Props_lt_transitive () // x < y < z
  ensures forall x, y, z :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
lemma Props_lt_add_is_lt () // x + a < y ==> x < y
  ensures forall x, y, a :: AbLt(AbAdd(x, a), y) ==> AbLt(x, y)

lemma Props_add_commutative () // x + y == y + x
  ensures forall x, y :: AbAdd(x, y) == AbAdd(y, x);
lemma Props_add_associative () // (x + y) + z == x + (y + z)
  ensures forall x, y, z :: AbAdd(AbAdd(x, y), z) == AbAdd(x, AbAdd(y, z))
lemma Props_add_addition () // x + a == y + a ==> x == y
  ensures forall x, y, a :: AbAdd(x, a) == AbAdd(y, a) <==> x == y
lemma Props_add_identity () // x + 0 == 0 + x == x
  ensures forall x :: AbAdd(x, int2adt(0)) == AbAdd(int2adt(0), x) == x

lemma Props_add_less_is_lt () // x = y + a && a < b ==> x < y + b
  ensures forall x, y, a, b :: (x == AbAdd(y, a)) && AbLt(a, b) ==> AbLt(x, AbAdd(y, b))
// Some instantiation
lemma Props_add_less_is_lt_param (x: AbInt, y: AbInt, a: AbInt, b: AbInt)
  // Props_add_less_is_lt_param(s, n, int2adt(llen), int2adt(len));
  ensures (x == AbAdd(y, a)) && AbLt(a, b) ==> AbLt(x, AbAdd(y, b))

lemma Props_add_is_leq () //  x + a == y ==> x < y || x == y
  ensures forall x, y, a :: (AbAdd(x, a) == y) ==> AbLt(x, y) || x == y
lemma Props_add_pos_is_neq () // x + Positive != x
  ensures forall x, a :: AbPos(a) ==> AbAdd(x, a) != x
lemma Props_add_pos_is_pos () // x + Positive is Positive
  ensures forall x, a :: AbPos(a) ==> AbPos(AbAdd(x, a)) 
lemma Props_add_pos_is_lt () // x < x + Positive
  ensures forall x, a :: AbPos(a) ==> AbLt(x, AbAdd(x, a));
lemma Props_add2sub () // x + y == z ==> x = z - y && y = z - x
  ensures forall x, y, z :: AbAdd(x, y) == z ==> AbSub(z, y) == x && AbSub(z, x) == y

lemma Props_add_sub_is_add () // x + j + (i - j) == x + i
    ensures forall x, i, j :: AbAdd(AbAdd(x, j), AbSub(i, j)) == AbAdd(x, i) // trigger may loop
    // ensures forall x: AbInt, i, j, k: int :: k == i - j ==> AbAdd(AbAdd(x, int2adt(j)), int2adt(k)) == AbAdd(x, int2adt(i))
// Some instantiation
lemma Props_add_sub_is_add_param(x: AbInt, i: AbInt, j: AbInt)
  // Props_add_sub_is_add_param(n, len, llen);
  ensures AbAdd(AbAdd(x, j), AbSub(i, j)) == AbAdd(x, i)

lemma Props_div_pos_is_pos () // Positive / 2 is Positive
  ensures forall x :: AbPos(x) <==> AbPos(AbDiv2(x))
lemma Props_div_add_leq_is_leq () // y <= x ==> (x+y)/2 <= x
  ensures forall x, y :: AbLt(y, x) || x == y ==> AbLt(AbDiv2(AbAdd(x, y)), x) || AbDiv2(AbAdd(x, y)) == x
lemma Props_div_add_leq_is_leq_param (x: AbInt, y: AbInt)
  ensures AbLt(y, x) || x == y ==> AbLt(AbDiv2(AbAdd(x, y)), x) || AbDiv2(AbAdd(x, y)) == x
lemma Props_div_addone_lt ()
  ensures forall x :: AbLt(int2adt(1), x) || x == int2adt(1) ==> AbLt(AbAdd(AbDiv2(x), int2adt(1)), x)
lemma Props_div_addone_lt_param (x: AbInt)
  ensures AbLt(int2adt(1), x) || x == int2adt(1) ==> AbLt(AbAdd(AbDiv2(x), int2adt(1)), x)

// lemma Props_unfold_int2adt (i: nat)
//   ensures i == 0 ==> int2adt(i) == int2adt(0)
//   ensures i != 0 ==> int2adt(i) == AbAdd(int2adt(1), int2adt(i-1))

function method Length(xs: List<AbInt>): AbInt
{
  match xs
  case Nil => int2adt(0)
  case Cons(_, tail) =>  AbAdd(int2adt(1), Length(tail))
}
 
function method Split(xs: List<AbInt>, b: AbInt): (List<AbInt>, List<AbInt>)
  ensures var r := Split(xs, b); Length(xs) == AbAdd(Length(r.0), Length(r.1))
  decreases xs
{
  Props_add_commutative ();
  Props_add_associative ();
  Props_add_identity ();
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
  Props_add_commutative ();
  Props_add_associative ();
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
  Props_add_addition ();
  Props_add_commutative ();
  Props_lt_addition ();
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
  Props_add_addition ();
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
  // assume AbLt(int2adt(len - 1), int2adt(len));
  // Try not to assign every element with AbAdd()
  // assert len != 0 ==> S == IntRange(lo, len - 1) + {AbAdd(lo, int2adt(len - 1))};
  assert forall x :: ((AbLt(lo, x) || lo == x) && AbLt(x, AbAdd(lo, len))) ==> x in S;
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
  Props_add_commutative ();
  if AbLt(int2adt(2), len) || int2adt(2) == len then
    var (L, R) := Split(xs, AbAdd(n, AbDiv2(len)));
    var llen := Length(L);
    Props_all_nonneg ();
    Props_lt_is_not_geq ();
    Props_int_pos(2); // AbInt0 < AbInt2
    Props_add_pos_is_lt ();
    if AbLt(llen, AbDiv2(len)) then
      Props_lt_transitive (); // AbInt0 < len
      Props_lt_add_is_lt ();
      Props_adt_dt_lt (llen, len);
      SMN(L, n, llen)
    else
      Props_div_pos_is_pos ();
      Props_add2sub ();
      Props_adt_dt_lt (AbSub(len, llen), len);
      SMN(R, AbAdd(n, llen), AbSub(len, llen))
  else if xs.Cons? then
    if xs.head == n then AbAdd(n, int2adt(1)) else n
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
    (AbLt(s, AbAdd(n, len)) || s == AbAdd(n, len)) &&
    s !in Elements(xs) &&
    forall x :: (AbLt(n, x) || n == x) && AbLt(x, s) ==> x in Elements(xs)
  decreases adt2dt(len)
{
  Props_add_commutative (); // x + y = y + x
  Props_all_nonneg ();
  Props_lt_is_not_geq (); // x < y <==> !x > y && x != y
  if AbLt(int2adt(2), len) || int2adt(2) == len {
    var (L, R) := Split(xs, AbAdd(n, AbDiv2(len)));
    Split_Correct(xs, AbAdd(n, AbDiv2(len)));
    var llen := Length(L);
    Elements_Property(L);  // NoDuplicates property
    var bound := IntRange(n, AbDiv2(len));
    Cardinality(Elements(L), bound);
    Props_int_pos(2); // 0 < 2
    Props_div_pos_is_pos ();
    Props_add_pos_is_lt (); // x < x + Positive
    Props_lt_add_is_lt (); // x + Postive < y ==> x < y
    if AbLt(llen, AbDiv2(len)) {
      var s := SMN(L, n, llen);
      Props_lt_transitive (); // x < y < z      
      Props_adt_dt_lt (llen, len); // decreases (pre: llen < len/2 < len)
      SMN_Correct(L, n, llen);
      Props_lt_addition (); // a < b ==> x + a < x + b: Lt(s, n+llen) ==> Lt(s, n+len)
      // Props_add_less_is_lt ();  // x = y + a && a < b ==> x < y + b: s==n+llen ==> Lt(s, n+len)
      Props_add_less_is_lt_param(s, n, llen, len); // no trigger loop
    } else {
      Props_add2sub ();
      Props_adt_dt_lt (AbSub(len, llen), len);
      var s := SMN(R, AbAdd(n, llen), AbSub(len, llen));
      SMN_Correct(R, AbAdd(n, llen), AbSub(len, llen));
      Props_add_is_leq (); // x + a == y ==> x < y || x == y: n+llen == s ==> Lt(n, s)
      // Props_add_sub_is_add();
      Props_add_sub_is_add_param(n, len, llen); // no trigger loop
      forall x | (AbLt(n, x) || n == x) && AbLt(x, s)
        ensures x in Elements(xs)
      {
        if AbLt(x, AbAdd(n, llen)) {
          SetEquality(Elements(L), bound);
        }
      }
    }
  } 
  else {
    Props_int_pos(1); // 0 < 1
    Props_2is1add1 ();
    Props_one_in_bound ();
    Props_add_identity ();
    Props_add_addition ();
    Props_add_pos_is_neq (); // x + Positive != x
    Props_add_is_leq (); // x + a == y ==> x < y || x == y
    Props_add_pos_is_pos (); // x + Positive = Positive
  }
}

function method SMN'(xs: List<AbInt>, n: AbInt, len: AbInt): AbInt
  requires len == Length(xs)
  decreases adt2dt(len)
{
  if xs == Nil then n
  else
    var half := AbDiv2(AbAdd(len, int2adt(1))); // half = (len+1)/2
    var (L, R) := Split(xs, AbAdd(n, half));
    var llen := Length(L);
    Props_int_pos(1); // 0 < 1
    Props_all_nonneg ();
    // Props_add_identity ();
    Props_add_pos_is_pos (); // x + Positive = Positive
    Props_add_pos_is_lt (); // x < x + Positive
    Props_gt0_geq1_param (len); // x > 0 ==> x >= 1
    Props_add_commutative ();
    Props_lt_transitive ();
    Props_div_add_leq_is_leq_param (len, int2adt(1));  // no trigger loop
    if AbLt(llen, half) then
      Props_adt_dt_lt (llen, len);
      SMN'(L, n, llen)
    else
      Props_add2sub ();
      Props_lt_is_not_geq ();
      Props_div_pos_is_pos ();
      Props_adt_dt_lt (AbSub(len, llen), len);
      SMN'(R, AbAdd(n, llen), AbSub(len, llen))
}

lemma SMN'_Correct(xs: List<AbInt>, n: AbInt, len: AbInt)
  requires NoDuplicates(xs)
  requires forall x :: x in Elements(xs) ==> (AbLt(n, x) || n == x)
  requires len == Length(xs)
  ensures var s := SMN'(xs, n, len);
    (AbLt(n, s) || n == s) &&
    (AbLt(s, AbAdd(n, len)) || s == AbAdd(n, len)) &&
    s !in Elements(xs) &&
    forall x ::(AbLt(n, x) || n == x) && AbLt(x, s) ==> x in Elements(xs)
  decreases adt2dt(len)
{
  Props_lt_is_not_geq (); // x < y <==> !x > y && x != y
  Props_add_identity ();
  if xs == Nil {
  } else {
    var half := AbDiv2(AbAdd(len, int2adt(1))); // half = (len+1)/2
    var (L, R) := Split(xs, AbAdd(n, half));
    Split_Correct(xs, AbAdd(n, half));
    var llen := Length(L);
    Elements_Property(L);  // use the NoDuplicates property
    var bound := IntRange(n, half);
    Cardinality(Elements(L), bound);
    Props_int_pos(1); // 0 < 1
    Props_all_nonneg ();
    Props_add_pos_is_pos (); // x + Positive = Positive
    Props_add_pos_is_lt (); // x < x + Positive
    Props_gt0_geq1_param (len); // x > 0 ==> x >= 1
    Props_add_commutative ();
    Props_lt_transitive ();
    Props_div_add_leq_is_leq_param (len, int2adt(1));  // no trigger loop
    if AbLt(llen, half) {
      var s := SMN'(L, n, llen);
      Props_adt_dt_lt (llen, len);
      SMN'_Correct(L, n, llen);
      Props_lt_addition ();
      Props_add_less_is_lt_param(s, n, llen, len); // no trigger loop
    } else {
      Props_add2sub ();
      Props_div_pos_is_pos ();
      assert llen == half;
      Props_adt_dt_lt (AbSub(len, llen), len);
      var s := SMN'(R, AbAdd(n, llen), AbSub(len, llen));
      SMN'_Correct(R, AbAdd(n, llen), AbSub(len, llen));
      Props_add_sub_is_add_param(n, len, llen); // no trigger loop
      forall x | (AbLt(n, x) || n == x) && AbLt(x, s)
        ensures x in Elements(xs)
      {
        if AbLt(x, AbAdd(n, llen)) {
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
    var half := AbAdd(AbDiv2(len), int2adt(1)); // half = len/2 + 1
    var (L, R) := Split(xs, AbAdd(n, half));
    var llen := Length(L);
    Props_int_pos(1); // 0 < 1
    Props_all_nonneg ();
    // Props_add_identity ();
    Props_add_pos_is_pos (); // x + Positive = Positive
    Props_add_pos_is_lt (); // x < x + Positive
    Props_gt0_geq1_param (len); // x > 0 ==> x >= 1
    Props_add_commutative ();
    Props_lt_transitive ();
    Props_div_addone_lt_param (len);
    assert AbLt(half, len);
    if AbLt(llen, half) then
      Props_adt_dt_lt (llen, len);
      SMN''(L, n, llen)
    else
      Props_add2sub ();
      Props_lt_is_not_geq ();
      Props_div_pos_is_pos ();
      Props_add_less_is_lt ();
      Props_adt_dt_lt (AbSub(len, llen), len);
      SMN''(R, AbAdd(n, llen), AbSub(len, llen))
}

lemma SMN''_Correct(xs: List<AbInt>, n: AbInt, len: AbInt)
  requires NoDuplicates(xs)
  requires forall x :: x in Elements(xs) ==> (AbLt(n, x) || n == x)
  requires len == Length(xs)
  ensures var s := SMN''(xs, n, len);
    (AbLt(n, s) || n == s) &&
    (AbLt(s, AbAdd(n, len)) || s == AbAdd(n, len)) &&
    s !in Elements(xs) &&
    forall x ::(AbLt(n, x) || n == x) && AbLt(x, s) ==> x in Elements(xs)
  decreases adt2dt(len)
{
  Props_lt_is_not_geq (); // x < y <==> !x > y && x != y
  Props_add_identity ();
  if xs == Nil {
  } else {
    var half := AbAdd(AbDiv2(len), int2adt(1)); // half = len/2 + 1
    var (L, R) := Split(xs, AbAdd(n, half));
    Split_Correct(xs, AbAdd(n, half));
    var llen := Length(L);
    Elements_Property(L);  // use the NoDuplicates property
    var bound := IntRange(n, half);
    Cardinality(Elements(L), bound);
    Props_int_pos(1); // 0 < 1
    Props_all_nonneg ();
    Props_add_pos_is_pos (); // x + Positive = Positive
    Props_add_pos_is_lt (); // x < x + Positive
    Props_gt0_geq1_param (len); // x > 0 ==> x >= 1
    Props_add_commutative ();
    Props_lt_transitive ();
    Props_div_addone_lt_param (len);
    if AbLt(llen, half) {
      var s := SMN''(L, n, llen);
      Props_adt_dt_lt (llen, len);
      SMN''_Correct(L, n, llen);
      Props_lt_addition ();
      Props_add_less_is_lt_param(s, n, llen, len); // no trigger loop
    } else {
      Props_add2sub ();
      Props_div_pos_is_pos ();
      Props_adt_dt_lt (AbSub(len, llen), len);
      var s := SMN''(R, AbAdd(n, llen), AbSub(len, llen));
      SMN''_Correct(R, AbAdd(n, llen), AbSub(len, llen));
      Props_add_sub_is_add_param(n, len, llen); // no trigger loop
      forall x | (AbLt(n, x) || n == x) && AbLt(x, s)
        ensures x in Elements(xs)
      {
        if AbLt(x, AbAdd(n, llen)) {
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
//   Props_add_associative ();
//   Props_add_identity ();
//   Props_add_commutative ();
//   Props_add_pos_is_pos ();
//   Props_int_pos(2);
//   Props_lt_transitive ();
//   Props_lt_is_not_geq ();
//   assert s == int2adt(0);
//   print s, " ";  // 0
//   var a := Cons(int2adt(2), Cons(int2adt(0), Nil));
//   Props_2is1add1 ();
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
