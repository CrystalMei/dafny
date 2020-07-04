// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "ADT-int.dfy"

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

import opened ADT`AB
import opened ADT'

/* Specific Properties */
lemma Concrete_AbAdd ()
  ensures AbAdd(I2A(8), I1) == I2A(9)
  ensures AbAdd(I2A(9), I1) == I2A(10)
  ensures AbAdd(I2A(11), I2A(10)) == I2A(21)

lemma Concrete_AbDiv ()
  requires I2A(9) != I0
  requires I2A(10) != I0
  ensures AbDiv(I2A(100), I2A(9)) == I2A(11)
  ensures AbDiv(I2A(100), I2A(10)) == I2A(10)

method Main()
{
  Props_pos (I1);
  Props_notneg ();
  Props_add_pos_is_pos ();
  Props_lt_gt_eq ();

  Concrete_AbAdd ();
  Concrete_AbDiv ();

  // v = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  var v := seq(10, _ => I0);
  // v' = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  var v' := VectorUpdate(10, v, (i,_) => I2A(i));
  assert |v'| == |v|;
  PrintSeq(v');
  // v' = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  v' := VectorUpdate(10, v', (_,x) => AbAdd(x, I2A(1)));
  PrintSeq(v');
  // assert (forall x :: x in v' ==> !AbIsZero(x));
  // v' = [100, 50, 33, 25, 20, 16, 14, 12, 11, 10]
  v' := VectorUpdate(10, v', (_,x) requires !AbIsZero(x) => AbDiv(I2A(100), x));
  PrintSeq(v');

  // u = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  var u := seq(10, _ => I2A(0));
  // u' = [100, 50, 33, 25, 20, 16, 14, 12, 11, 10]
  u := VectorUpdate(10, u, (i,_) requires 0 <= i < 10 => v'[i]);
  PrintSeq(u);

  // z = [0, 0, 0, 0, 0, 0, 0, 0, 0]
  var z := seq(9, _ => I2A(0));
  // z' = [150, 83, 58, 45, 35, 30, 26, 23, 21]
  z := VectorUpdate(9, z, (i,_) requires 0 <= i < 9 => AbAdd(u[i], u[i+1]));
  PrintSeq(z);
  assert z[8] == I2A(21);
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
