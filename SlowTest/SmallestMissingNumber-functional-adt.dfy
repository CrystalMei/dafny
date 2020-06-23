// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// standard definitions

type AbInt(==)
ghost const Ab0 : AbInt
ghost const Ab1 : AbInt
ghost const Ab2 : AbInt
ghost const Ab3 : AbInt
ghost const Ab4 : AbInt
ghost const Ab5 : AbInt
ghost const Ab6 : AbInt
ghost const Ab7 : AbInt
ghost const Ab8 : AbInt

function method AbSucc (ghost n: AbInt) : (r: AbInt)
  ensures n == Ab0 ==> r == Ab1
  ensures n == Ab1 ==> r == Ab2
  ensures n == Ab2 ==> r == Ab3
  ensures n == Ab3 ==> r == Ab5
  ensures n == Ab4 ==> r == Ab5
  ensures n == Ab5 ==> r == Ab6
  ensures n == Ab6 ==> r == Ab7
  ensures n == Ab7 ==> r == Ab8

predicate AbEq(n: AbInt, m: AbInt)
  ensures forall x :: AbEq(x, x)
  ensures forall x, y :: AbEq(x, y) == AbEq(y, x)
  ensures forall x, y, z :: AbEq(x, y) && AbEq(y, z) ==> AbEq(x, z) 

predicate AbLt(n: AbInt, m: AbInt)
  ensures forall x, y, z :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
  ensures AbLt(Ab0, Ab1) && AbLt(Ab1, Ab2) && AbLt(Ab2, Ab3) && AbLt(Ab3, Ab4) && AbLt(Ab4, Ab5) && AbLt(Ab5, Ab6) && AbLt(Ab6, Ab7) && AbLt(Ab7, Ab8)
  ensures !AbEq(n, m)

predicate AbLeq (n: AbInt, m: AbInt)
  ensures AbEq(n, m) || AbLt(n, m)

function method AbAdd(ghost n: AbInt, ghost m: AbInt) : (r: AbInt)
  ensures forall x, y :: AbAdd(x, y) == AbAdd(y, x)
  ensures forall x, y, z :: AbAdd(AbAdd(x, y), z) == AbAdd(x, AbAdd(y, z))
  ensures forall x :: AbAdd(x, Ab0) == AbAdd(Ab0, x) == x

datatype List<X> = Nil | Cons(head: X, tail: List<X>)

method Main() {
  var xs := Nil;
  var s := SmallestMissingNumber(xs);
  assert s == Ab0;
  print s, " ";  // 0
  var a := Cons(Ab2, Cons(Ab0, Nil));
//   print SmallestMissingNumber(a), " ";  // 1
  a := Cons(Ab3, Cons(Ab1, a));
//   print SmallestMissingNumber(a), " ";  // 4
  a := Cons(Ab7, Cons(Ab4, Cons(Ab6, a)));
//   print SmallestMissingNumber(a), "\n";  // 5
}

function method Length(xs: List): nat
{
  match xs
  case Nil => 0
  case Cons(_, tail) => 1 + Length(tail)
}

function method SmallestMissingNumber(xs: List<AbInt>): AbInt
{
  SMN(xs, Ab0, Length(xs))
}

function method SMN(xs: List<AbInt>, n: AbInt, len: nat): AbInt
  requires len == Length(xs)
  decreases len
{
  if 2 <= len then
    var (L, R) := Split(xs, n + len/2); //TODO
    var llen := Length(L);
    if llen < len/2 then
      SMN(L, n, llen)
    else
      SMN(R, n + llen, len - llen) //TODO
  else if xs.Cons? then
    if AbEq(xs.head, n) then AbSucc(n) else n // TODO
  else
    n
}

function method Split(xs: List<AbInt>, b: AbInt): (List<AbInt>, List<AbInt>)
  ensures var r := Split(xs, b); Length(xs) == Length(r.0) + Length(r.1)
{
  match xs
  case Nil => (Nil, Nil)
  case Cons(x, tail) =>
    var (L, R) := Split(tail, b);
    if AbLt(x, b) then //TODO
      (Cons(x, L), R)
    else
      (L, Cons(x, R))
}

function Elements(xs: List): set
{
  match xs
  case Nil => {}
  case Cons(x, tail) => {x} + Elements(tail)
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

// proof of lemmas supporting proof of main theorem

lemma SmallestMissingNumber_Correct(xs: List<AbInt>)
  requires NoDuplicates(xs)
  ensures var s := SmallestMissingNumber(xs);
    s !in Elements(xs) &&
    forall x :: AbLeq(Ab0, x) && AbLt(x, s) ==> x in Elements(xs)
{
  SMN_Correct(xs, Ab0, Length(xs));
}

// element, len, index -> abstract type
lemma SMN_Correct(xs: List<AbInt>, n: AbInt, len: nat)
  requires NoDuplicates(xs)
  requires forall x :: x in Elements(xs) ==> AbLeq(n, x)
  requires len == Length(xs)
  ensures var s := SMN(xs, n, len);
    AbLeq(n, s) && AbLeq(s, n + len) && // TODO
    s !in Elements(xs) &&
    forall x :: AbLeq(n, x) && AbLt(x, s) ==> x in Elements(xs)
  decreases len
{
  if 2 <= len {
    var (L, R) := Split(xs, n + len/2); // TODO
    Split_Correct(xs, n + len/2); // TODO
    var llen := Length(L);
    Elements_Property(L);  // this is where we need the NoDuplicates property
    var bound := IntRange(n, len/2); //TODO
    Cardinality(Elements(L), bound);
    if llen < len/2 {
      SMN_Correct(L, n, llen);
    } else {
      var s := SMN(R, n + llen, len - llen); //TODO
      SMN_Correct(R, n + llen, len - llen); //TODO
      forall x | AbLeq(n, x) && AbLt(x, s)
        ensures x in Elements(xs)
      {
        if AbLt(x, n + llen) { // TODO
          SetEquality(Elements(L), bound);
        }
      }
    }
  }
}

lemma Split_Correct(xs: List<AbInt>, b: AbInt)
  requires NoDuplicates(xs)
  ensures var r := Split(xs, b);
    Elements(r.0) == (set x | x in Elements(xs) && AbLt(x, b)) &&
    Elements(r.1) == (set x | x in Elements(xs) && AbLeq(b, x)) &&
    NoDuplicates(r.0) && NoDuplicates(r.1)
{
  match xs
  case Nil =>
  case Cons(_, tail) =>
    Split_Correct(tail, b);
}

lemma Elements_Property(xs: List)
  requires NoDuplicates(xs)
  ensures |Elements(xs)| == Length(xs)
{
}

// TODO
function IntRange(lo: AbInt, len: nat): set<AbInt>
  ensures |IntRange(lo, len)| == len
{
  var S := set x | AbLeq(lo, x) && AbLt(x, lo + len); // TODO
  assert len != 0 ==> S == IntRange(lo, len - 1) + {lo+len-1}; // TODO
  S
}

// // Here is an alternative version, with a different splitting
// // condition (using the ceiling of len/2.0 instead of the floor)
// // and only two cases.
// function method SMN'(xs: List<nat>, n: nat, len: nat): nat
//   requires len == Length(xs)
//   decreases len
// {
//   if xs == Nil then
//     n
//   else
//     var half := (len + 1) / 2;
//     var (L, R) := Split(xs, n + half);
//     var llen := Length(L);
//     if llen < half then
//       SMN'(L, n, llen)
//     else
//       SMN'(R, n + llen, len - llen)
// }

// // Here is yet one more version. This time, the splitting condition
// // is 1 more than then floor of len/2.0. This is the version of the
// // algorithm in Richard Bird's book.
// function method SMN''(xs: List<nat>, n: nat, len: nat): nat
//   requires len == Length(xs)
//   decreases len
// {
//   if xs == Nil then
//     n
//   else
//     var half := len / 2 + 1;
//     var (L, R) := Split(xs, n + half);
//     var llen := Length(L);
//     if llen < half then
//       SMN''(L, n, llen)
//     else
//       SMN''(R, n + llen, len - llen)
// }

// // ----- Proofs of alternative versions

// lemma SMN'_Correct(xs: List<nat>, n: nat, len: nat)
//   requires NoDuplicates(xs)
//   requires forall x :: x in Elements(xs) ==> n <= x
//   requires len == Length(xs)
//   ensures var s := SMN'(xs, n, len);
//     n <= s <= n + len &&
//     s !in Elements(xs) &&
//     forall x :: n <= x < s ==> x in Elements(xs)
//   decreases len
// {
//   if xs == Nil {
//   } else {
//     var half := (len + 1) / 2;
//     var (L, R) := Split(xs, n + half);
//     Split_Correct(xs, n + half);
//     var llen := Length(L);
//     Elements_Property(L);  // use the NoDuplicates property
//     var bound := IntRange(n, half);
//     Cardinality(Elements(L), bound);
//     if llen < half {
//       SMN'_Correct(L, n, llen);
//     } else {
//       var s := SMN'(R, n + llen, len - llen);
//       SMN'_Correct(R, n + llen, len - llen);
//       forall x | n <= x < s
//         ensures x in Elements(xs)
//       {
//         if x < n + llen {
//           SetEquality(Elements(L), bound);
//         }
//       }
//     }
//   }
// }

// lemma SMN''_Correct(xs: List<nat>, n: nat, len: nat)
//   requires NoDuplicates(xs)
//   requires forall x :: x in Elements(xs) ==> n <= x
//   requires len == Length(xs)
//   ensures var s := SMN''(xs, n, len);
//     n <= s <= n + len &&
//     s !in Elements(xs) &&
//     forall x :: n <= x < s ==> x in Elements(xs)
//   decreases len
// {
//   if xs == Nil {
//   } else {
//     var half := len / 2 + 1;
//     var (L, R) := Split(xs, n + half);
//     Split_Correct(xs, n + half);
//     var llen := Length(L);
//     Elements_Property(L);  // use the NoDuplicates property
//     var bound := IntRange(n, half);
//     Cardinality(Elements(L), bound);
//     if llen < half {
//       SMN''_Correct(L, n, llen);
//     } else {
//       var s := SMN''(R, n + llen, len - llen);
//       SMN''_Correct(R, n + llen, len - llen);
//       forall x | n <= x < s
//         ensures x in Elements(xs)
//       {
//         if x < n + llen {
//           SetEquality(Elements(L), bound);
//         }
//       }
//     }
//   }
// }
