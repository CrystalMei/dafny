// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// this is a rather verbose version of the VectorUpdate method
type AbInt(==)
ghost const Ab0 : AbInt
ghost const Ab1 : AbInt
// ghost const Ab2 : AbInt
// ghost const Ab3 : AbInt
// ghost const Ab4 : AbInt
// ghost const Ab5 : AbInt
// ghost const Ab6 : AbInt
// ghost const Ab7 : AbInt
ghost const Ab8 : AbInt
ghost const Ab9 : AbInt
ghost const Ab10 : AbInt
ghost const Ab11 : AbInt
ghost const Ab21 : AbInt
ghost const Ab100 : AbInt

predicate IsZero (n: AbInt)
  ensures n == Ab0 ==> true
  // ensures n != Ab0 ==> false
  ensures n == Ab1 /* || n == Ab2 || n == Ab3 || n == Ab4 || n == Ab5 || n == Ab6 || n == Ab7 */ || n == Ab8 || n == Ab9 || n == Ab10 ==> false

function method Add (ghost n: AbInt, ghost m: AbInt) : (r: AbInt)
  ensures n == Ab8 && m == Ab1 ==> r == Ab9
  ensures n == Ab9 && m == Ab1 ==> r == Ab10
  ensures n == Ab11 && m == Ab10 ==> r == Ab21

function method Div (ghost n: AbInt, ghost m: AbInt) : (r: AbInt)
  requires IsZero(m)
  ensures n == Ab100 && m == Ab9 ==> r == Ab11
  ensures n == Ab100 && m == Ab10 ==> r == Ab10

method VectorUpdate(N: int, ghost a : seq<AbInt>, f : (int,AbInt) ~> AbInt) returns (ghost a': seq<AbInt>)
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

function method int2adt (n: int) : (r: AbInt)
  ensures n == 0 ==> r == Ab0
  // ensures n == 1 ==> r == Ab1
  // ensures n == 2 ==> r == Ab2
  // ensures n == 3 ==> r == Ab3
  // ensures n == 4 ==> r == Ab4
  // ensures n == 5 ==> r == Ab5
  // ensures n == 6 ==> r == Ab6
  // ensures n == 7 ==> r == Ab7
  ensures n == 8 ==> r == Ab8
  ensures n == 9 ==> r == Ab9  

method Main()
{
  // assert (Ab0 == Ab1); // failed
  // assert (Ab0 != Ab1); // failed
  // v = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  ghost var v := seq(10, _ => Ab0);
  // v' = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  ghost var v' := VectorUpdate(10, v, (i,_) => int2adt(i));
  assert |v'| == |v|;
  PrintSeq(v');
  // v' = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  v' := VectorUpdate(10, v', (_,x) => Add(x, Ab1));
  PrintSeq(v');
  // v' = [100, 50, 33, 25, 20, 16, 14, 12, 11, 10]
  v' := VectorUpdate(10, v', (_,x) requires !IsZero(x) => Div(Ab100, x));
  PrintSeq(v');

  // u = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  ghost var u := seq(10, _ => Ab0);
  // u' = [100, 50, 33, 25, 20, 16, 14, 12, 11, 10]
  // u := VectorUpdate(10, u, (i,_) requires 0 <= i < 10 => v'[i]);
  // PrintSeq(u');

  // z = [0, 0, 0, 0, 0, 0, 0, 0, 0]
  ghost var z := seq(9, _ => Ab0);
  // z' = [150, 83, 58, 45, 35, 30, 26, 23, 21]
  z := VectorUpdate(9, z, (i,_) requires 0 <= i < 9 => Add(v'[i], v'[i+1]));
  PrintSeq(z);

  assert z[8] == Ab21;
}

method PrintSeq(ghost a : seq<AbInt>)
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
