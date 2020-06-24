// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// this is a rather verbose version of the VectorUpdate method
type AbInt(==)
// const {:extern} Ab0 : AbInt

function method int2adt (n: int) : AbInt
predicate AbIsZero (n: AbInt) {n == int2adt(0)}
predicate AbNonNeg (n: AbInt) { true }
predicate AbPos (n: AbInt) {AbNonNeg(n) && !AbIsZero(n)}

// tedious function
// TODO: if we can say int2adt(0) is unique, shorten this func!
function method AbAdd (n: AbInt, m: AbInt) : (r: AbInt)
  ensures n == int2adt(8) && m == int2adt(1) ==> r == int2adt(9)
  ensures n == int2adt(9) && m == int2adt(1) ==> r == int2adt(10)
  ensures n == int2adt(11) && m == int2adt(10) ==> r == int2adt(21)

function method AbDiv (n: AbInt, m: AbInt) : (r: AbInt)
  requires m != int2adt(0)
  ensures n == int2adt(100) && m == int2adt(9) ==> r == int2adt(11)
  ensures n == int2adt(100) && m == int2adt(10) ==> r == int2adt(10)

method VectorUpdate<A>(N: int, a : seq<A>, f : (int,A) ~> A) returns (a': seq<A>)
  requires N == |a|
  requires forall j :: 0 <= j < N ==> f.requires(j,a[j])
  ensures |a| == |a'|
  ensures forall j :: 0 <= j < N ==> a'[j] == f(j,a[j])
{
  var i := 0;
  a' := a;
  while i < N
    invariant 0 <= i <= N
    invariant |a| == |a'|
    invariant forall j :: 0 <= j < N ==> f.requires(j,a[j])
    invariant forall j :: i <= j < N ==> f.requires(j,a'[j])
    invariant forall j :: i <= j < N ==> a'[j] == a[j]
    invariant forall j :: 0 <= j < i ==> a'[j] == f(j,a[j])
  {
    a' := a'[i := f(i,a[i])];
    i := i + 1;
  }
}

lemma Assume_Pos()
  // ensures forall x, y :: AbAdd(x, y) == AbAdd(y, x) // w/ or w/o this, no change.
  ensures forall x, y :: AbPos(y) ==> AbPos(AbAdd(x, y))

method Main()
{
  assume AbPos(int2adt(1));
  Assume_Pos();
  // v = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  var v := seq(10, _ => int2adt(0));
  // v' = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  var v' := VectorUpdate(10, v, (i,_) => int2adt(i));
  assert |v'| == |v|;
  PrintSeq(v');
  // v' = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  v' := VectorUpdate(10, v', (_,x) => AbAdd(x, int2adt(1)));
  PrintSeq(v');
  assert (forall x :: x in v' ==> x != int2adt(0));
  // v' = [100, 50, 33, 25, 20, 16, 14, 12, 11, 10]
  v' := VectorUpdate(10, v', (_,x) requires !AbIsZero(x) => AbDiv(int2adt(100), x));
  PrintSeq(v');

  // u = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  var u := seq(10, _ => int2adt(0));
  // u' = [100, 50, 33, 25, 20, 16, 14, 12, 11, 10]
  u := VectorUpdate(10, u, (i,_) requires 0 <= i < 10 => v'[i]);
  PrintSeq(u);

  // z = [0, 0, 0, 0, 0, 0, 0, 0, 0]
  var z := seq(9, _ => int2adt(0));
  // z' = [150, 83, 58, 45, 35, 30, 26, 23, 21]
  z := VectorUpdate(9, z, (i,_) requires 0 <= i < 9 => AbAdd(u[i], u[i+1]));
  PrintSeq(z);
  assert z[8] == int2adt(21);
}

method PrintSeq(a : seq<AbInt>)
{
  // var i := 0;
  // while i < |a| {
  //   if i != 0 {
	//   print ", ";
	// }
  //   print a[i];
  //   i := i + 1;
  // }
  // print "\n";
}
