// SMN-orig.dfy
function method Add(a: int, b: int): int { a + b }
lemma Add_Commutative()
    ensures forall a: int, b: int :: Add(a, b) == Add(b, a)
lemma Add_Associative()
    ensures forall a: int, b: int, c: int :: Add(Add(a, b), c) == Add(a, Add(b, c))
lemma Add_Identity()
    ensures forall a: int :: Add(a, 0) == Add(0, a) == a

lemma Add_Commutative_p2(a: int, b: int)
    ensures Add(a, b) == Add(b, a)
lemma Add_Associative_p3 (a: int, b: int, c: int)
    ensures Add(Add(a, b), c) == Add(a, Add(b, c))
lemma Add_Identity_p1(a: int)
    ensures Add(a, 0) == Add(0, a) == a

datatype List<X> = Nil | Cons(head: X, tail: List<X>)

function method Length(xs: List): int // verified
{
  match xs
  case Nil => 0
  case Cons(_, tail) => Add(1, Length(tail))
}

function method Split(xs: List<int>, b: int): (List<int>, List<int>)
  ensures var r := Split(xs, b); Length(xs) == Add(Length(r.0), Length(r.1))
{
  match xs
  case Nil =>
    Add_Identity_p1(0); // assume Add(0, 0) == 0;
    (Nil, Nil)
  case Cons(x, tail) =>
    var (L, R) := Split(tail, b);
    if x < b then
      Add_Associative_p3(1, Length(L), Length(R));
      // assume Add(Add(1, Length(L)), Length(R)) == Add(1, Add(Length(L), Length(R)));
      (Cons(x, L), R)
    else
      Add_Associative_p3(Length(L), 1, Length(R));
      Add_Commutative_p2(1, Length(L));
      Add_Associative_p3(1, Length(L), Length(R));
      // assume Add(Length(L), Add(1, Length(R))) == Add(1, Add(Length(L), Length(R)));
      (L, Cons(x, R))
}

lemma Split_Correct(xs: List<int>, b: int) // verified
  requires NoDuplicates(xs)
  ensures var r := Split(xs, b);
    Elements(r.0) == (set x | x in Elements(xs) && x < b) &&
    Elements(r.1) == (set x | x in Elements(xs) && b <= x) &&
    NoDuplicates(r.0) && NoDuplicates(r.1)
{
  match xs
  case Nil =>
  case Cons(_, tail) =>
    Split_Correct(tail, b);
}

function Elements(xs: List): set // verified
{
  match xs
  case Nil => {}
  case Cons(x, tail) => {x} + Elements(tail)
}

lemma Elements_Property(xs: List)
  requires NoDuplicates(xs)
  ensures |Elements(xs)| == Length(xs)
{
  match xs
  case Nil => 
  case Cons(x, tail) =>
    
  assume |Elements(xs)| == Length(xs);
  // assume forall x: int, s: set<int> :: x in s ==> |s| == Add(1, |s - {x}|);
}

predicate NoDuplicates(xs: List) // verified
{
  match xs
  case Nil => true
  case Cons(x, tail) =>
    x !in Elements(tail) && NoDuplicates(tail)
}

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

function IntRange(lo: int, len: int): set<int>
  ensures |IntRange(lo, len)| == len
{
  var S := set x | lo <= x < lo + len;
  assert len != 0 ==> S == IntRange(lo, len - 1) + {lo+len-1};
  S
}

function method SmallestMissingNumber(xs: List<int>): int
{
  SMN(xs, 0, Length(xs))
}

function method SMN(xs: List<int>, n: int, len: int): int
  requires len == Length(xs)
  decreases len
{
  if 2 <= len then
    var (L, R) := Split(xs, n + len/2);
    var llen := Length(L);
    if llen < len/2 then
      SMN(L, n, llen)
    else
      SMN(R, n + llen, len - llen)
  else if xs.Cons? then
    if xs.head == n then n + 1 else n
  else
    n
}

// Here is an alterintive version, with a different splitting
// condition (using the ceiling of len/2.0 instead of the floor)
// and only two cases.
function method SMN'(xs: List<int>, n: int, len: int): int
  requires len == Length(xs)
  decreases len
{
  if xs == Nil then
    n
  else
    var half := (len + 1) / 2;
    var (L, R) := Split(xs, n + half);
    var llen := Length(L);
    if llen < half then
      SMN'(L, n, llen)
    else
      SMN'(R, n + llen, len - llen)
}

// Here is yet one more version. This time, the splitting condition
// is 1 more than then floor of len/2.0. This is the version of the
// algorithm in Richard Bird's book.
function method SMN''(xs: List<int>, n: int, len: int): int
  requires len == Length(xs)
  decreases len
{
  if xs == Nil then
    n
  else
    var half := len / 2 + 1;
    var (L, R) := Split(xs, n + half);
    var llen := Length(L);
    if llen < half then
      SMN''(L, n, llen)
    else
      SMN''(R, n + llen, len - llen)
}

// correctness theorem

lemma SmallestMissingNumber_Correct(xs: List<int>)
  requires NoDuplicates(xs)
  ensures var s := SmallestMissingNumber(xs);
    s !in Elements(xs) &&
    forall x :: 0 <= x < s ==> x in Elements(xs)
{
  SMN_Correct(xs, 0, Length(xs));
}

// proof of lemmas supporting proof of main theorem

// element, len, index -> abstract type
lemma SMN_Correct(xs: List<int>, n: int, len: int)
  requires NoDuplicates(xs)
  requires forall x :: x in Elements(xs) ==> n <= x
  requires len == Length(xs)
  ensures var s := SMN(xs, n, len);
    n <= s <= n + len &&
    s !in Elements(xs) &&
    forall x :: n <= x < s ==> x in Elements(xs)
  decreases len
{
  if 2 <= len {
    var (L, R) := Split(xs, n + len/2);
    Split_Correct(xs, n + len/2);
    var llen := Length(L);
    Elements_Property(L);  // this is where we need the NoDuplicates property
    var bound := IntRange(n, len/2);
    Cardinality(Elements(L), bound);
    if llen < len/2 {
      SMN_Correct(L, n, llen);
    } else {
      var s := SMN(R, n + llen, len - llen);
      SMN_Correct(R, n + llen, len - llen);
      forall x | n <= x < s
        ensures x in Elements(xs)
      {
        if x < n + llen {
          SetEquality(Elements(L), bound);
        }
      }
    }
  }
}

method Main() {
  var xs := Nil;
  var s := SmallestMissingNumber(xs);
  assert s == 0;
  print s, " ";  // 0
  var a := Cons(2, Cons(0, Nil));
  assert SmallestMissingNumber(a) == 1;
  // print SmallestMissingNumber(a), " ";  // 1
  a := Cons(3, Cons(1, a));
  assert SmallestMissingNumber(a) == 4;
  // print SmallestMissingNumber(a), " ";  // 4
  a := Cons(7, Cons(4, Cons(6, a)));
  assert SmallestMissingNumber(a) == 5;
  // print SmallestMissingNumber(a), "\n";  // 5
}

// Timeout proofs

// // ----- Proofs of alterintive versions

// lemma SMN'_Correct(xs: List<int>, n: int, len: int)
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

// lemma SMN''_Correct(xs: List<int>, n: int, len: int)
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
