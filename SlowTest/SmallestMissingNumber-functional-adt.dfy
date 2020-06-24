// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// standard definitions

type AbInt(==)
datatype List<X> = Nil | Cons(head: X, tail: List<X>)

// const {:extern} Ab0 : AbInt
// const {:extern} Ab1 : AbInt
// const {:extern} Ab2 : AbInt
// const {:extern} Ab3 : AbInt
// const {:extern} Ab4 : AbInt
// const {:extern} Ab5 : AbInt
// const {:extern} Ab6 : AbInt
// const {:extern} Ab7 : AbInt
// const {:extern} Ab8 : AbInt

function method int2adt (n: int) : (r: AbInt)
predicate IsZero (n: AbInt) {n == int2adt(0)}
predicate NonNeg (n: AbInt) { true }
predicate AbPos (n: AbInt) {NonNeg(n) && !IsZero(n)}

function method AbLt(n: AbInt, m: AbInt) : bool
function method AbAdd(n: AbInt, m: AbInt) : (r: AbInt)

// Set generation: lo <= x < lo+len
// TODO: if len is also an ADT, what should I do here?
function method AbBoundSet(lo: AbInt, len: nat): (S: set<AbInt>)
  ensures |S| == len
  ensures S == set x | 0 <= x < len :: AbAdd(lo, int2adt(x))


/* Properties */
lemma Props()
  /* AbLt */
  ensures forall x, y, z :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
  // ensures forall n :: !AbLt(n, n)
  // ensures forall x, y :: AbPos(y) ==> AbLt(x, AbAdd(x, y))
  ensures forall x, y :: AbLt(x, y) <==> !(AbLt(y, x) || x == y)
  ensures forall x :: AbLt(int2adt(0), x) || x == int2adt(0)
  // ensures forall x : AbInt, y : int :: y != 0 ==> AbLt (x, AbAdd(x, int2adt(y)))
  ensures forall x, y, z :: AbLt(y, z) ==> AbLt(AbAdd(x, y), AbAdd(x, z))
  // TODO: may not have integer here?
  ensures forall x, y : int :: x < y ==> AbLt(int2adt(x), int2adt(y))

  /* AbAdd */
  // ensures forall x, y :: AbAdd(x, y) == AbAdd(y, x)
  // ensures forall x, y, z :: AbAdd(AbAdd(x, y), z) == AbAdd(x, AbAdd(y, z))
  // ensures forall x :: AbAdd(x, int2adt(0)) == AbAdd(int2adt(0), x) == x
  ensures forall x : AbInt, y, z : int :: AbAdd(AbAdd(x, int2adt(y)), int2adt(z-y)) == AbAdd(x, int2adt(z)) // trigger may loop

lemma Props2()
  ensures forall x, y, n1, n2 :: (AbAdd(y, n1) == x) && AbLt(n1, n2) ==> AbLt(x, AbAdd(y, n2))
  ensures forall x, y, n :: AbAdd(y, n) == x ==> AbLt(y, x) || y == x

lemma Set_Props(S1 : set<AbInt>, n: AbInt, l: nat)
  /* Set */
  ensures var S2 := AbBoundSet(n, l);
    forall x :: x in S1 && AbLt(x, AbAdd(n, int2adt(l))) ==> S1 <= S2

lemma Set_Props2 (xs: set<AbInt>, b: AbInt, s: AbInt)
  ensures
    var S1 := (set x | x in xs && AbLt(x, b));
    var S2 := (set x | x in xs && !AbLt(x, b));
    s !in S1 ==> s !in xs

method Main() {
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

function method Length(xs: List): nat
{
  match xs
  case Nil => 0
  case Cons(_, tail) => 1 + Length(tail)
}

function method SmallestMissingNumber(xs: List<AbInt>): AbInt
{
  SMN(xs, int2adt(0), Length(xs))
}

function method SMN(xs: List<AbInt>, n: AbInt, len: nat): AbInt
  requires len == Length(xs)
  decreases len
{
  if 2 <= len then
    var (L, R) := Split(xs, AbAdd(n, int2adt(len/2))); // ADT
    var llen := Length(L);
    if llen < len/2 then
      SMN(L, n, llen)
    else
      SMN(R, AbAdd(n, int2adt(llen)), len - llen) // ADT
  else if xs.Cons? then
    if xs.head == n then AbAdd(n, int2adt(1)) else n // ADT
  else
    n
}

// verified
// function method SMN'(xs: List<AbInt>, n: AbInt, len: nat): AbInt
//   requires len == Length(xs)
//   decreases len
// {
//   if xs == Nil then
//     n
//   else
//     var half := (len + 1) / 2;
//     var (L, R) := Split(xs, AbAdd(n, int2adt(half)));
//     var llen := Length(L);
//     if llen < half then
//       SMN'(L, n, llen)
//     else
//       SMN'(R, AbAdd(n, int2adt(llen)), len - llen)
// }

// function method SMN''(xs: List<AbInt>, n: AbInt, len: nat): AbInt
//   requires len == Length(xs)
//   decreases len
// {
//   if xs == Nil then
//     n
//   else
//     var half := len / 2 + 1;
//     var (L, R) := Split(xs, AbAdd(n, int2adt(half)));
//     var llen := Length(L);
//     if llen < half then
//       SMN''(L, n, llen)
//     else
//       SMN''(R, AbAdd(n, int2adt(llen)), len - llen)
// }

function method Split(xs: List<AbInt>, b: AbInt): (List<AbInt>, List<AbInt>)
  ensures var r := Split(xs, b); Length(xs) == Length(r.0) + Length(r.1)
{
  match xs
  case Nil => (Nil, Nil)
  case Cons(x, tail) =>
    var (L, R) := Split(tail, b);
    if AbLt(x, b) then // ADT
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
  ensures |Elements(xs)| == Length(xs)
{
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

function IntRange(lo: AbInt, len: nat): set<AbInt>
  ensures |IntRange(lo, len)| == len
{
  var S := AbBoundSet(lo, len); // ADT
  assert len != 0 ==> S == IntRange(lo, len - 1) + {AbAdd(lo, int2adt(len - 1))}; // ADT
  // TODO: can we check this with Props()? Nop, because we don't know AbLt(int2adt(x), int2adt(y))
  // Props ();
  // assert forall x :: x in S ==> (AbLt(lo, x) || lo == x) && AbLt(x, AbAdd(lo, int2adt(len)));
  S
}

// proof of lemmas supporting proof of main theorem

lemma SmallestMissingNumber_Correct(xs: List<AbInt>)
  requires NoDuplicates(xs)
  ensures var s := SmallestMissingNumber(xs);
    s !in Elements(xs) &&
    forall x :: (AbLt(int2adt(0), x) || int2adt(0) == x) && AbLt(x, s) ==> x in Elements(xs)
{
  Props ();
  SMN_Correct(xs, int2adt(0), Length(xs));
}

// element, len, index -> abstract type
lemma SMN_Correct(xs: List<AbInt>, n: AbInt, len: nat)
  requires NoDuplicates(xs)
  requires forall x :: x in Elements(xs) ==> (AbLt(n, x) || n == x)
  requires len == Length(xs)
  ensures var s := SMN(xs, n, len);
    (AbLt(n, s) || n == s) && // failed
    (AbLt(s, AbAdd(n, int2adt(len))) || s == AbAdd(n, int2adt(len))) && // failed
    s !in Elements(xs) && // failed
    forall x ::(AbLt(n, x) || n == x) && AbLt(x, s) ==> x in Elements(xs) //failed
  decreases len
{
  if 2 <= len {
    Props ();
    var (L, R) := Split(xs, AbAdd(n, int2adt(len/2)));
    Split_Correct(xs, AbAdd(n, int2adt(len/2)));
    var llen := Length(L);
    Elements_Property(L);  // this is where we need the NoDuplicates property
    var bound := IntRange(n, len/2);
    Set_Props(Elements(L), n, len/2); // ADT Props
    Cardinality(Elements(L), bound);
    Props (); // Why I duplicate the assumptions here, it failed so quick?
    if llen < len/2 {
      var s := SMN(L, n, llen);
      SMN_Correct(L, n, llen);
      Set_Props2(Elements(xs), AbAdd(n, int2adt(len/2)), s);
      Props2();
    } else {
      Props2();
      var s := SMN(R, AbAdd(n, int2adt(llen)), len - llen);
      SMN_Correct(R, AbAdd(n, int2adt(llen)), len - llen);
      forall x | (AbLt(n, x) || n == x) && AbLt(x, s)
        ensures x in Elements(xs) // failed
      {
        if AbLt(x, AbAdd(n, int2adt(llen))) {
          SetEquality(Elements(L), bound);
        }
      }
    }
  }
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
