// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<X> = Nil | Cons(head: X, tail: List<X>)

type AbInt(==)
function method int2adt (n: int) : (r: AbInt)
// function method adt2int (n: AbInt) : (r: int)
//   decreases n
//   ensures n == int2adt(0) ==> r == 0
//   ensures forall x :: AbAdd(int2adt(1), x) == n ==> r == 1 + adt2int(x)

predicate AbIsZero (n: AbInt) {n == int2adt(0)}
predicate AbNonNeg (n: AbInt) { true }
predicate AbPos (n: AbInt) {AbNonNeg(n) && !AbIsZero(n)}

function method AbLt(n: AbInt, m: AbInt) : bool
function method AbAdd(n: AbInt, m: AbInt) : (r: AbInt)
function method AbSub(n: AbInt, m: AbInt) : (r: AbInt)
function method AbDiv2(n: AbInt): (r: AbInt)
  ensures AbLt(AbAdd(r, r), n) || AbAdd(r, r) == n

// Set generation: lo <= x < lo+len
// experiment with more trigger options
function method AbBoundSet(lo: AbInt, len: AbInt): (S: set<AbInt>)
  ensures int2adt(|S|) == len
  ensures forall x :: (AbLt(lo, x) || lo == x) && AbLt(x, AbAdd(lo, len)) <==> x in S
  // Try not to assign every element with AbAdd()
  // ensures S == set x | 0 <= x < len :: AbAdd(lo, int2adt(x))


/* Properties */
lemma Props_int_pos(a: int)
  ensures AbPos(int2adt(a))
lemma Props_int_cmp_lt(a: int, b: int) // Lt(a, b)
  ensures AbLt(int2adt(a), int2adt(b))

lemma Props_plus_minus_is_eq ()
    ensures forall x: AbInt, i, j: int :: AbAdd(AbAdd(x, int2adt(j)), int2adt(i-j)) == AbAdd(x, int2adt(i)) // trigger may loop
    // ensures forall x: AbInt, i, j, k: int :: k == i - j ==> AbAdd(AbAdd(x, int2adt(j)), int2adt(k)) == AbAdd(x, int2adt(i))
// Props_plus_minus_is_eq_param(n, len, llen);
lemma Props_plus_minus_is_eq_param(x: AbInt, i: AbInt, j: AbInt)
  ensures AbAdd(AbAdd(x, j), AbSub(i, j)) == AbAdd(x, i)
// Props_eq_less_is_lt_param(s, n, int2adt(llen), int2adt(len));
lemma Props_eq_less_is_lt_param (x: AbInt, y: AbInt, a: AbInt, b: AbInt)
  ensures (x == AbAdd(y, a)) && AbLt(a, b) ==> AbLt(x, AbAdd(y, b))

lemma Props ()
  // Prop_all_leq_zero ()
  ensures forall x :: AbLt(int2adt(0), x) || x == int2adt(0)
  // Props_lt_is_not_geq ()
  ensures forall x, y :: AbLt(x, y) <==> !(AbLt(y, x) || x == y)
  // Props_lt_addition ()
  ensures forall x, a, b:: AbLt(a, b) ==> AbLt(AbAdd(x, a), AbAdd(x, b))
  // Props_lt_transitive ()
  ensures forall x, y, z :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
  // Props_plus_zero ()
  ensures forall x :: AbAdd(x, int2adt(0)) == AbAdd(int2adt(0), x) == x
  // Props_eq_less_is_lt ()
  ensures forall x, y, a, b :: (x == AbAdd(y, a)) && AbLt(a, b) ==> AbLt(x, AbAdd(y, b))
  // Props_plus_eq_is_lt ()
  ensures forall x, y, a :: (AbAdd(x, a) == y) && AbNonNeg(a) ==> AbLt(x, y)
  // Props_plus_lt_is_lt ()
  ensures forall x, y, a :: AbLt(AbAdd(x, a), y) && AbNonNeg(a) ==> AbLt(x, y)
  // Props_plus_pos_is_neq ()
  ensures forall x, a :: AbPos(a) ==> AbAdd(x, a) != x
  // Props_one_in_bound ()
  ensures forall a, x :: (AbLt(a, x) || a == x) && (AbLt(x, AbAdd(a, int2adt(1)))) ==> a == x
  // // Props_plus_minus_is_eq ()
  // ensures forall x: AbInt, i, j: int :: AbAdd(AbAdd(x, int2adt(j)), int2adt(i-j)) == AbAdd(x, int2adt(i)) // trigger may loop
  ensures forall x: AbInt, i, j, k: int :: k == i - j ==> AbAdd(AbAdd(x, int2adt(j)), int2adt(k)) == AbAdd(x, int2adt(i))

// duplicate with Props ()
// Note: if comment out, SMN_Correct doesn't finish.
// lemma Prop_all_leq_zero ()
//   ensures forall x :: AbLt(int2adt(0), x) || x == int2adt(0)
// lemma Props_lt_is_not_geq ()
//   ensures forall x, y :: AbLt(x, y) <==> !(AbLt(y, x) || x == y)
// lemma Props_lt_addition () // trigger problem?
//   ensures forall x, a, b:: AbLt(a, b) ==> AbLt(AbAdd(x, a), AbAdd(x, b))
// lemma Props_lt_transitive ()
//   ensures forall x, y, z :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
// lemma Props_plus_zero ()
//   ensures forall x :: AbAdd(x, int2adt(0)) == AbAdd(int2adt(0), x) == x
// lemma Props_eq_less_is_lt ()
//   ensures forall x, y, a, b :: (x == AbAdd(y, a)) && AbLt(a, b) ==> AbLt(x, AbAdd(y, b))
// lemma Props_plus_eq_is_lt ()
//   ensures forall x, y, a :: (AbAdd(x, a) == y) && AbNonNeg(a) ==> AbLt(x, y)
// lemma Props_plus_lt_is_lt ()
//   ensures forall x, y, a :: AbLt(AbAdd(x, a), y) && AbNonNeg(a) ==> AbLt(x, y)
// lemma Props_plus_pos_is_neq ()
//   ensures forall x, a :: AbPos(a) ==> AbAdd(x, a) != x
// lemma Props_one_in_bound ()
//   ensures forall a, x :: (AbLt(a, x) || a == x) && (AbLt(x, AbAdd(a, int2adt(1)))) ==> a == x

// // Props_eq_less_is_lt_param(s, n, int2adt(llen), int2adt(len));
// lemma Props_eq_less_is_lt_param (x: AbInt, y: AbInt, a: AbInt, b: AbInt)
//   ensures (x == AbAdd(y, a)) && AbLt(a, b) ==> AbLt(x, AbAdd(y, b))

lemma Props_two_is_one_plus_one ()
  ensures int2adt(2) == AbAdd(int2adt(1), int2adt(1))
lemma Props_plus_commutative ()
  ensures forall x, y :: AbAdd(x, y) == AbAdd(y, x);
lemma Props_plus_associative ()
  ensures forall x, y, z :: AbAdd(AbAdd(x, y), z) == AbAdd(x, AbAdd(y, z))
lemma Props_plus_pos_is_lt ()
  ensures forall x, a :: AbPos(a) ==> AbLt(x, AbAdd(x, a));
lemma Props_plus_and_minus ()
  ensures forall x, y, z :: AbAdd(x, y) == z ==> AbSub(z, y) == x && AbSub(z, x) == y
lemma Props_unfold_int2adt (i: nat)
  ensures i == 0 ==> int2adt(i) == int2adt(0)
  ensures i != 0 ==> int2adt(i) == AbAdd(int2adt(1), int2adt(i-1))

function method Length(xs: List): AbInt
{
  match xs
  case Nil => int2adt(0)
  case Cons(_, tail) => AbAdd(int2adt(1), Length(tail))
}

function method SmallestMissingNumber(xs: List<AbInt>): AbInt
{
  SMN(xs, int2adt(0), Length(xs))
}

function method SMN(xs: List<AbInt>, n: AbInt, len: AbInt): AbInt
  requires len == Length(xs)
  decreases adt2int(Length(xs))
{
  Props_two_is_one_plus_one ();
  Props_plus_commutative ();
  Props_plus_and_minus ();
  if AbLt(int2adt(2), len) || int2adt(2) == len then
    var (L, R) := Split(xs, AbAdd(n, AbDiv2(len)));
    var llen := Length(L);
    if AbLt(llen, AbDiv2(len)) then
      SMN(L, n, llen)
    else
      SMN(R, AbAdd(n, llen), AbSub(len, llen))
  else if xs.Cons? then
    if xs.head == n then AbAdd(n, int2adt(1)) else n
  else
    n
}

function method SMN'(xs: List<AbInt>, n: AbInt, len: AbInt): AbInt
  requires len == Length(xs)
  // decreases adt2int(Length(xs))
{
  Props_two_is_one_plus_one ();
  Props_plus_commutative ();
  Props_plus_and_minus ();
  if xs == Nil then
    n
  else
    var half := AbDiv2(AbAdd(len, int2adt(1)));
    var (L, R) := Split(xs, AbAdd(n, half));
    var llen := Length(L);
    if AbLt(llen, half) then
      SMN'(L, n, llen)
    else
      SMN'(R, AbAdd(n, llen), AbSub(len, llen))
}

function method SMN''(xs: List<AbInt>, n: AbInt, len: AbInt): AbInt
  requires len == Length(xs)
  decreases xs
{
  Props_two_is_one_plus_one ();
  Props_plus_commutative ();
  Props_plus_and_minus ();
  if xs == Nil then
    n
  else
    var half := AbAdd(AbDiv2(len), int2adt(1));
    var (L, R) := Split(xs, AbAdd(n, half));
    var llen := Length(L);
    if AbLt(llen, half) then
      SMN''(L, n, llen)
    else
      SMN''(R, AbAdd(n, llen), AbSub(len, llen))
}

function method Split(xs: List<AbInt>, b: AbInt): (List<AbInt>, List<AbInt>)
  ensures var r := Split(xs, b); Length(xs) == AbAdd(Length(r.0), Length(r.1))
  decreases xs
{
  Props ();
  Props_plus_commutative ();
  Props_plus_associative ();
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

function Elements(xs: List): set
{
  match xs
  case Nil => {}
  case Cons(x, tail) => {x} + Elements(tail)
}

lemma Elements_Property(xs: List)
  requires NoDuplicates(xs)
  ensures int2adt(|Elements(xs)|) == Length(xs)
{
  Props_unfold_int2adt(|Elements(xs)|);
}

predicate NoDuplicates(xs: List)
{
  match xs
  case Nil => true
  case Cons(x, tail) =>
    x !in Elements(tail) && NoDuplicates(tail)
}

// standard theorems and their proofs

lemma Cardinality(A: set, B: set)
  requires A <= B
  ensures |A| <= |B|
{
  if A != {} {
    var x :| x in A;
    Cardinality(A - {x}, B - {x});
  }
}

lemma SetEquality(A: set, B: set)
  requires A <= B && |A| == |B|
  ensures A == B
{
  if A == {} {
  } else {
    var x :| x in A;
    SetEquality(A - {x}, B - {x});
  }
}

function IntRange(lo: AbInt, len: AbInt): set<AbInt>
  ensures int2adt(|IntRange(lo, len)|) == len
{
  var S := AbBoundSet(lo, len);
  // assume AbLt(int2adt(len - 1), int2adt(len));
  // Try not to assign every element with AbAdd()
  // assert len != 0 ==> S == IntRange(lo, len - 1) + {AbAdd(lo, int2adt(len - 1))};
  assert forall x :: ((AbLt(lo, x) || lo == x) && AbLt(x, AbAdd(lo, len))) ==> x in S;
  S
}

// // proof of lemmas supporting proof of main theorem

// lemma SmallestMissingNumber_Correct(xs: List<AbInt>)
//   requires NoDuplicates(xs)
//   ensures var s := SmallestMissingNumber(xs);
//     s !in Elements(xs) &&
//     forall x :: (AbLt(int2adt(0), x) || int2adt(0) == x) && AbLt(x, s) ==> x in Elements(xs)
// {
//   Props ();
//   SMN_Correct(xs, int2adt(0), Length(xs));
// }

// // element, len, index -> abstract type
// lemma SMN_Correct(xs: List<AbInt>, n: AbInt, len: AbInt)
//   requires NoDuplicates(xs)
//   requires forall x :: x in Elements(xs) ==> (AbLt(n, x) || n == x)
//   requires len == Length(xs)
//   ensures var s := SMN(xs, n, len);
//     (AbLt(n, s) || n == s) &&
//     (AbLt(s, AbAdd(n, len)) || s == AbAdd(n, len)) &&
//     s !in Elements(xs) &&
//     forall x ::(AbLt(n, x) || n == x) && AbLt(x, s) ==> x in Elements(xs)
//   decreases len
// {
//   Props ();
//   // Props_two_is_one_plus_one ();
//   // Props_plus_commutative ();
//   // Props_plus_and_minus ();
//   if AbLt(int2adt(2), len) || int2adt(2) == len {
//     var (L, R) := Split(xs, AbAdd(n, AbDiv2(len)));
//     Split_Correct(xs, AbAdd(n, AbDiv2(len)));
//     var llen := Length(L);
//     Elements_Property(L);  // NoDuplicates property
//     var bound := IntRange(n, AbDiv2(len));
//     // Props_lt_is_not_geq ();
//     Cardinality(Elements(L), bound);
//     if AbLt(llen, AbDiv2(len)) {
//       var s := SMN(L, n, llen);
//       SMN_Correct(L, n, llen);
//       // Props_lt_addition (); // Lt(s, n+llen) ==> Lt(s, n+len)
//       // Props_lt_transitive ();
//       // Props_eq_less_is_lt (); // s==n+llen ==> Lt(s, n+len)
//       // Note: instantiation for no trigger loop
//       Props_eq_less_is_lt_param(s, n, llen, len);
//     } else {
//       var s := SMN(R, AbAdd(n, llen), AbSub(len, llen));
//       SMN_Correct(R, AbAdd(n, llen), AbSub(len, llen));
//       // Props_plus_lt_is_lt (); // Lt(n+llen, s) ==> Lt(n, s)      
//       // Props_plus_is_leq (); // n+llen == s ==> Lt(n, s)
//       // Props_plus_minus_is_eq();
//       // Note: instantiation for no trigger loop
//       Props_plus_minus_is_eq_param(n, len, llen);
//       forall x | (AbLt(n, x) || n == x) && AbLt(x, s)
//         ensures x in Elements(xs)
//       {
//         if AbLt(x, AbAdd(n, llen)) {
//           SetEquality(Elements(L), bound);
//         }
//       }
//     }
//   } 
//   else {
//     Props_int_pos(1);
//     // Props_plus_is_leq ();
//     // Props_plus_pos_is_neq ();
//     // Props_one_in_bound ();
//     // Props_lt_is_not_geq ();
//     // Props_plus_zero ();
//   }
// }

// lemma SMN'_Correct(xs: List<AbInt>, n: AbInt, len: nat)
//   requires NoDuplicates(xs)
//   requires forall x :: x in Elements(xs) ==> (AbLt(n, x) || n == x)
//   requires len == Length(xs)
//   ensures var s := SMN'(xs, n, len);
//     (AbLt(n, s) || n == s) &&
//     (AbLt(s, AbAdd(n, int2adt(len))) || s == AbAdd(n, int2adt(len))) &&
//     s !in Elements(xs) &&
//     forall x :: (AbLt(n, x) || n == x) && AbLt(x, s) ==> x in Elements(xs)
//   decreases len
// { 
//   Props ();
//   if xs == Nil {
//   } else {
//     var half := (len + 1) / 2;
//     var (L, R) := Split(xs, AbAdd(n, int2adt(half)));
//     Split_Correct(xs, AbAdd(n, int2adt(half)));
//     var llen := Length(L);
//     Elements_Property(L);  // use the NoDuplicates property
//     var bound := IntRange(n, half);
//     Cardinality(Elements(L), bound);
//     if llen < half {
//       var s := SMN'(L, n, llen);
//       SMN'_Correct(L, n, llen);
//       Props_int_cmp_lt(llen, half);
//       Props_int_cmp_lt(llen, len);
//       // Note: instantiation for no trigger loop
//       Props_eq_less_is_lt_param(s, n, int2adt(llen), int2adt(len));
//     } else {
//       var s := SMN'(R, AbAdd(n, int2adt(llen)), len - llen);
//       SMN'_Correct(R, AbAdd(n, int2adt(llen)), len - llen);
//       // Note: instantiation for no trigger loop
//       Props_plus_minus_is_eq_param(n, len, llen);
//       forall x | (AbLt(n, x) || n == x) && AbLt(x, s)
//         ensures x in Elements(xs)
//       {
//         if AbLt(x, AbAdd(n, int2adt(llen))) {
//           SetEquality(Elements(L), bound);
//         }
//       }
//     }
//   }
// }

// lemma SMN''_Correct(xs: List<AbInt>, n: AbInt, len: nat)
//   requires NoDuplicates(xs)
//   requires forall x :: x in Elements(xs) ==> (AbLt(n, x) || n == x)
//   requires len == Length(xs)
//   ensures var s := SMN''(xs, n, len);
//     (AbLt(n, s) || n == s) &&
//     (AbLt(s, AbAdd(n, int2adt(len))) || s == AbAdd(n, int2adt(len))) &&
//     s !in Elements(xs) &&
//     forall x :: (AbLt(n, x) || n == x) && AbLt(x, s) ==> x in Elements(xs)
//   decreases len
// {
//   Props ();
//   if xs == Nil {
//   } else {
//     var half := len / 2 + 1;
//     var (L, R) := Split(xs, AbAdd(n, int2adt(half)));
//     Split_Correct(xs, AbAdd(n, int2adt(half)));
//     var llen := Length(L);
//     Elements_Property(L);  // use the NoDuplicates property
//     var bound := IntRange(n, half);
//     Cardinality(Elements(L), bound);
//     if llen < half {
//       var s := SMN''(L, n, llen);
//       SMN''_Correct(L, n, llen);
//       Props_int_cmp_lt(llen, half);
//       Props_int_cmp_lt(llen, len);
//       // Note: instantiation for no trigger loop
//       Props_eq_less_is_lt_param(s, n, int2adt(llen), int2adt(len));
//     } else {
//       var s := SMN''(R, AbAdd(n, int2adt(llen)), len - llen);
//       SMN''_Correct(R, AbAdd(n, int2adt(llen)), len - llen);
//       // Note: instantiation for no trigger loop
//       Props_plus_minus_is_eq_param(n, len, llen);
//       forall x | (AbLt(n, x) || n == x) && AbLt(x, s)
//         ensures x in Elements(xs)
//       {
//         if AbLt(x, AbAdd(n, int2adt(llen))) {
//           SetEquality(Elements(L), bound);
//         }
//       }
//     }
//   }
// }

// TODO: need more concrete props to make it verified.
method Main() {
  Props();
  Props_plus_minus_is_eq ();

  // Note: this assumption is wrong.
  assume forall x, y, a :: (AbAdd(x, a) == y) && AbNonNeg(a) ==> AbLt(x, y);

  var xs := Nil;
  var s := SmallestMissingNumber(xs);
  assert s == int2adt(0);
  print s, " ";  // 0
  var a := Cons(int2adt(2), Cons(int2adt(0), Nil));
  // assert SmallestMissingNumber(a) == int2adt(1);
  // print SmallestMissingNumber(a), " ";  // 1
  a := Cons(int2adt(3), Cons(int2adt(1), a));
  // assert SmallestMissingNumber(a) == int2adt(4);
//   print SmallestMissingNumber(a), " ";  // 4
  a := Cons(int2adt(7), Cons(int2adt(4), Cons(int2adt(6), a)));
  // assert SmallestMissingNumber(a) == int2adt(5);
//   print SmallestMissingNumber(a), "\n";  // 5
}