// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "ADT-int.dfy"
datatype List<X> = Nil | Cons(head: X, tail: List<X>)

import opened ADT`Basic
import opened ADT_Int
import opened ADT_Set

function method Length(xs: List<AbInt>): AbInt
{
  match xs
  case Nil => I0
  case Cons(_, tail) => AbAdd(Length(tail), I1)
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
  Set_Props_len_element();
  Set_Props_len_empty ();
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
  ensures AbLeq(AbSetLen(A), AbSetLen(B))
{
  Props_notneg ();
  Set_Props_len ();
  Set_Props_len_element ();
  Set_Props_len_empty ();
  Props_lt_addition ();
  Props_add_addition ();
  Props_add_commutative ();
  if A != {} {
    var x :| x in A;
    Cardinality(A - {x}, B - {x});
  }
}

lemma SetEquality(A: set<AbInt>, B: set<AbInt>)
  requires A <= B && AbSetLen(A) == AbSetLen(B)
  ensures A == B
{
  Set_Props_len ();
  Set_Props_len_element ();
  Set_Props_len_empty ();
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
  Props_add2sub ();
  Props_add_sub_is_orig ();
  var S := AbBoundSet(lo, AbAdd(lo, len));
  // Try not to assign every element with AbAdd()
  // assert len != 0 ==> S == IntRange(lo, len - 1) + {AbAdd(lo, I2A(len - 1))};
  assert forall x :: (AbLeq(lo, x) && AbLt(x, AbAdd(lo, len))) ==> x in S;
  S
}

function method SmallestMissingNumber(xs: List<AbInt>): AbInt
{
  SMN(xs, I0, Length(xs))
}

function method SMN(xs: List<AbInt>, n: AbInt, len: AbInt): AbInt
  requires len == Length(xs)
  decreases A2D(len)
{
  Props_add_commutative ();
  if AbLeq(I2, len) then
    var (L, R) := Split(xs, AbAdd(n, AbDiv2(len)));
    var llen := Length(L);

    if AbLt(llen, AbDiv2(len)) then
      // len / 2 < len
      Props_pos(I2); // I0 < I2
      Props_lt_transitive (); // I0 < I2 < len
      Props_div_lt (); // x >= 2 ==> x / 2 < x
      Props_adt_dt_lt (llen, len);
      SMN(L, n, llen)
    else
      Props_lt_is_not_leq_p2 (llen, AbDiv2(len));
      // 0 < len / 2
      Props_div_pos2 (); // x >= 2 ==> x / 2 > 0
      Props_lt_transitive (); // 0 < len / 2 < llen
      Props_add2sub ();
      Props_add_pos_is_lt ();
      Props_adt_dt_lt (AbSub(len, llen), len);
      SMN(R, AbAdd(n, llen), AbSub(len, llen))
  else if xs.Cons? then
    if xs.head == n then AbAdd(n, I1) else n
  else
    n
}

// proof of lemmas supporting proof of main theorem

lemma SmallestMissingNumber_Correct(xs: List<AbInt>)
  requires NoDuplicates(xs)
  ensures var s := SmallestMissingNumber(xs);
    s !in Elements(xs) &&
    forall x :: AbLeqLt(x, I0, s) ==> x in Elements(xs)
{
  forall x | x in Elements(xs)
    ensures AbLeq(I0, x)
    { Props_notneg(); }
  SMN_Correct(xs, I0, Length(xs));
}

// element, len, index -> abstract type
lemma SMN_Correct(xs: List<AbInt>, n: AbInt, len: AbInt)
  requires NoDuplicates(xs)
  requires forall x :: x in Elements(xs) ==> AbLeq(n, x)
  requires len == Length(xs)
  ensures var s := SMN(xs, n, len);
    AbLeq(n, s) &&
    AbLeq(s, AbAdd(n, len)) &&
    s !in Elements(xs) &&
    forall x :: AbLeqLt(x, n, s) ==> x in Elements(xs)
  decreases A2D(len)
{
  Props_notneg();
  Props_add_commutative ();
  if AbLeq(I2, len) {
    var (L, R) := Split(xs, AbAdd(n, AbDiv2(len)));
    Split_Correct(xs, AbAdd(n, AbDiv2(len)));
    var llen := Length(L);
    Elements_Property(L);  // NoDuplicates property
    var bound := IntRange(n, AbDiv2(len));
    Cardinality(Elements(L), bound);
    
    if AbLt(llen, AbDiv2(len)) {
      var s := SMN(L, n, llen);
      // len / 2 < len
      Props_pos(I2); // I0 < I2
      Props_lt_transitive (); // I0 < I2 < len
      Props_div_lt (); // x >= 2 ==> x / 2 < x
      Props_adt_dt_lt (llen, len); // decreases (pre: llen < len/2 < len)
      SMN_Correct(L, n, llen);

      Props_lt_addition (); // a < b ==> x + a < x + b: Lt(s, n+llen) ==> Lt(s, n+len)
      Props_add_lt_is_lt_p4(s, n, llen, len); // x = y + a && a < b ==> x < y + b: s==n+llen ==> Lt(s, n+len)
    } else {
      // 0 < len / 2
      Props_div_pos2 (); // x >= 2 ==> x / 2 > 0
      Props_lt_transitive (); // 0 < len / 2 < llen
      Props_add2sub ();
      Props_add_pos_is_lt ();
      Props_adt_dt_lt (AbSub(len, llen), len);
      var s := SMN(R, AbAdd(n, llen), AbSub(len, llen));
      Props_lt_is_not_leq_py (AbAdd(n, llen));
      SMN_Correct(R, AbAdd(n, llen), AbSub(len, llen));

      Props_add_notneg_is_leq (); // x + a == y ==> x < y || x == y: n+llen == s ==> Lt(n, s)
      Props_add_sub_is_add_p3(n, len, llen); // no trigger loop
      forall x | (AbLt(n, x) || n == x) && AbLt(x, s)
        ensures x in Elements(xs)
      {
        if AbLt(x, AbAdd(n, llen)) {
          SetEquality(Elements(L), bound);
        }
      }
    }
  } 
  else if xs.Cons? {
    Props_pos(I1); // 0 < 1
    Props_2is1add1 ();
    Props_lt_is_not_leq ();
    Props_one_in_bound_p2 (I1, len);
    Props_add_notneg_is_leq (); // x + a == y ==> x <= y
    Props_add_pos_is_lt (); // x < x + Positive
    if xs.head == n {
      Props_add_identity ();
      Props_one_in_bound ();
    } else { }
  } else {
    Props_lt_is_not_leq ();
    Props_add_identity ();
  }
}

function method SMN'(xs: List<AbInt>, n: AbInt, len: AbInt): AbInt
  requires len == Length(xs)
  decreases A2D(len)
{
  if xs == Nil then n
  else
    var half := AbDiv2(AbAdd(len, I1)); // half = (len+1)/2
    var (L, R) := Split(xs, AbAdd(n, half));
    var llen := Length(L);
    if AbLt(llen, half) then
      Props_pos(I1); // 0 < 1
      Props_notneg ();
      Props_add_identity ();
      Props_add_pos_is_pos (); // x + Positive = Positive
      Props_lt2leq_p2 (I0, len); // len > 0 ==> len >= 1
      Props_div_leq_p2 (len, I1);  // len >= 1 ==> (len+1)/2 <= len
      Props_lt_transitive (); // llen < (len+1)/2 < len
      Props_adt_dt_lt (llen, len);
      SMN'(L, n, llen)
    else
      Props_pos(I1); // 0 < 1
      Props_notneg ();
      Props_add_identity ();
      Props_add_pos_is_pos (); // x + Positive = Positive
      Props_lt2leq_p2 (I0, len); // len > 0 ==> len >= 1
      Props_div_pos1 (); // (len+1)/2 > 0
      Props_lt_transitive (); // 0 < (len+1)/2 < llen
      Props_add_sub_is_orig ();
      Props_add_pos_is_lt ();
      Props_adt_dt_lt (AbSub(len, llen), len);
      Props_add2sub ();
      SMN'(R, AbAdd(n, llen), AbSub(len, llen))
}

lemma SMN'_Correct(xs: List<AbInt>, n: AbInt, len: AbInt)
  requires NoDuplicates(xs)
  requires forall x :: x in Elements(xs) ==> AbLeq(n, x)
  requires len == Length(xs)
  ensures var s := SMN'(xs, n, len);
    AbLeq(n, s) &&
    AbLeq(s, AbAdd(n, len)) &&
    s !in Elements(xs) &&
    forall x :: AbLeqLt(x, n, s) ==> x in Elements(xs)
  decreases A2D(len)
{
  Props_add_commutative ();
  if xs == Nil {
    Props_add_identity ();
    Props_lt_is_not_leq ();
  } else {
    var half := AbDiv2(AbAdd(len, I1)); // half = (len+1)/2
    var (L, R) := Split(xs, AbAdd(n, half));
    Split_Correct(xs, AbAdd(n, half));
    var llen := Length(L);
    Elements_Property(L);  // use the NoDuplicates property
    var bound := IntRange(n, half);
    Cardinality(Elements(L), bound);
    if AbLt(llen, half) {
      var s := SMN'(L, n, llen);
      Props_pos(I1); // 0 < 1
      Props_notneg();
      Props_add_identity ();
      Props_add_pos_is_pos (); // x + Positive = Positive
      Props_lt2leq_p2 (I0, len); // len > 0 ==> len >= 1
      Props_div_leq_p2 (len, I1);  // len >= 1 ==> (len+1)/2 <= len
      Props_lt_transitive (); // llen < (len+1)/2 < len
      Props_adt_dt_lt (llen, len);
      SMN'_Correct(L, n, llen);

      Props_lt_addition (); // a < b ==> x + a < x + b: Lt(s, n+llen) ==> Lt(s, n+len)
      Props_add_lt_is_lt_p4(s, n, llen, len); // x = y + a && a < b ==> x < y + b: s==n+llen ==> Lt(s, n+len)
    } else {
      Props_pos(I1); // 0 < 1
      Props_notneg();
      Props_add_identity ();
      Props_add_pos_is_pos (); // x + Positive = Positive
      Props_lt2leq_p2 (I0, len); // len > 0 ==> len >= 1
      Props_div_pos1 (); // (len+1)/2 > 0
      Props_lt_transitive (); // 0 < (len+1)/2 < llen
      Props_add_sub_is_orig ();
      Props_add_pos_is_lt ();
      Props_adt_dt_lt (AbSub(len, llen), len);
      Props_add2sub ();
      var s := SMN'(R, AbAdd(n, llen), AbSub(len, llen));
      Props_lt_is_not_leq_py (AbAdd(n, llen));
      SMN'_Correct(R, AbAdd(n, llen), AbSub(len, llen));

      Props_add_sub_is_add_p3(n, len, llen); // no trigger loop
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
  decreases A2D(len)
{
  if xs == Nil then n
  else
    var half := AbAdd(AbDiv2(len), I1); // half = len/2 + 1
    var (L, R) := Split(xs, AbAdd(n, half));
    var llen := Length(L);
    if AbLt(llen, half) then
      Props_pos(I1); // 0 < 1
      Props_notneg ();
      Props_add_identity ();
      Props_add_pos_is_pos (); // x + Positive = Positive
      Props_lt2leq_p2 (I0, len); // len > 0 ==> len >= 1
      Props_div_add1_leq_p1 (len);
      Props_lt_transitive ();
      Props_adt_dt_lt (llen, len);
      SMN''(L, n, llen)
    else
      Props_pos(I1); // 0 < 1
      Props_notneg ();
      Props_add_identity ();
      Props_add_pos_is_pos (); // x + Positive = Positive
      Props_lt2leq_p2 (I0, len); // len > 0 ==> len >= 1
      Props_add_pos_is_lt (); // x < x + Positive
      Props_lt_transitive (); // len/2 + 1 > 0
      Props_add_sub_is_orig ();
      Props_adt_dt_lt (AbSub(len, llen), len);
      Props_add2sub ();
      SMN''(R, AbAdd(n, llen), AbSub(len, llen))
}

lemma SMN''_Correct(xs: List<AbInt>, n: AbInt, len: AbInt)
  requires NoDuplicates(xs)
  requires forall x :: x in Elements(xs) ==> AbLeq(n, x)
  requires len == Length(xs)
  ensures var s := SMN''(xs, n, len);
    AbLeq(n, s) &&
    AbLeq(s, AbAdd(n, len)) &&
    s !in Elements(xs) &&
    forall x :: AbLeqLt(x, n, s) ==> x in Elements(xs)
  decreases A2D(len)
{
  Props_add_commutative ();
  if xs == Nil {
    Props_lt_is_not_leq (); // x < y <==> !x > y && x != y
    Props_add_identity ();
  } else {
    var half := AbAdd(AbDiv2(len), I1); // half = len/2 + 1
    var (L, R) := Split(xs, AbAdd(n, half));
    Split_Correct(xs, AbAdd(n, half));
    var llen := Length(L);
    Elements_Property(L);  // use the NoDuplicates property
    var bound := IntRange(n, half);
    Cardinality(Elements(L), bound);
    if AbLt(llen, half) {
      var s := SMN''(L, n, llen);
      Props_pos(I1); // 0 < 1
      Props_notneg ();
      Props_add_identity ();
      Props_add_pos_is_pos (); // x + Positive = Positive
      Props_lt2leq_p2 (I0, len); // len > 0 ==> len >= 1
      Props_div_add1_leq_p1 (len);
      Props_lt_transitive ();
      Props_adt_dt_lt (llen, len);
      SMN''_Correct(L, n, llen);

      Props_lt_addition (); // a < b ==> x + a < x + b: Lt(s, n+llen) ==> Lt(s, n+len)
      Props_add_lt_is_lt_p4(s, n, llen, len); // x = y + a && a < b ==> x < y + b: s==n+llen ==> Lt(s, n+len)
    } else {
      Props_pos(I1); // 0 < 1
      Props_notneg ();
      Props_add_identity ();
      Props_add_pos_is_pos (); // x + Positive = Positive
      Props_lt2leq_p2 (I0, len); // len > 0 ==> len >= 1
      Props_add_pos_is_lt (); // x < x + Positive
      Props_lt_transitive (); // len/2 + 1 > 0
      Props_add_sub_is_orig ();
      Props_adt_dt_lt (AbSub(len, llen), len);
      Props_add2sub ();
      var s := SMN''(R, AbAdd(n, llen), AbSub(len, llen));
      Props_lt_is_not_leq_py (AbAdd(n, llen));
      SMN''_Correct(R, AbAdd(n, llen), AbSub(len, llen));

      Props_add_sub_is_add_p3(n, len, llen); // no trigger loop
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
//   assert Length(xs) == I0;
//   var s := SmallestMissingNumber(xs);
//   Props_notneg ();
//   Props_add_associative ();
//   Props_add_identity ();
//   Props_add_commutative ();
//   Props_add_pos_is_pos ();
//   Props_pos(I2);
//   Props_lt_transitive ();
//   Props_lt_is_not_leq ();
//   assert s == I0;
//   print s, " ";  // 0
//   var a := Cons(I2, Cons(I0, Nil));
//   Props_2is1add1 ();
//   assume I1 == AbDiv2(I2);
//   assume AbLt(I0, I1);
//   assume AbLt(I1, I2);
//   // assert SmallestMissingNumbxer(a) == I1;
//   // print SmallestMissingNumber(a), " ";  // 1
//   a := Cons(I2A(3), Cons(I1, a));
//   // assert SmallestMissingNumber(a) == I2A(4);
// //   print SmallestMissingNumber(a), " ";  // 4
//   a := Cons(I2A(7), Cons(I2A(4), Cons(I2A(6), a)));
//   // assert SmallestMissingNumber(a) == I2A(5);
// //   print SmallestMissingNumber(a), "\n";  // 5
// }
