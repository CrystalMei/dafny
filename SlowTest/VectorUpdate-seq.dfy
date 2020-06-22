// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// this is a rather verbose version of the VectorUpdate method
method VectorUpdate<A>(N: int, a : seq<A>, f : (int,A) ~> A) returns (a': seq<A>)
  requires N == |a|
  requires forall j :: 0 <= j < N ==> f.requires(j,a[j])
//   requires forall j :: 0 <= j < N ==> a !in f.reads(j,a[j])
//   modifies a
  ensures |a| == |a'|
  ensures forall j :: 0 <= j < N ==> a'[j] == f(j,old(a[j]))
{
  var i := 0;
  a' := a;
  while i < N
    invariant 0 <= i <= N
    invariant |a| == |a'|
    invariant forall j :: i <= j < N ==> f.requires(j,a[j])
    invariant forall j :: 0 <= j < N ==> f.requires(j,old(a[j]))
    // invariant forall j :: i <= j < N ==> a !in f.reads(j,a[j])
    invariant forall j :: i <= j < N ==> a'[j] == old(a[j])
    invariant forall j :: 0 <= j < i ==> a'[j] == f(j,old(a[j]))
  {
    a' := a'[i := f(i,a[i])];
    i := i + 1;
  }
}

// here's a shorter version of the method above
method VectorUpdate'<A>(a : seq<A>, f : (int,A) ~> A) returns (a': seq<A>)
  requires forall j :: 0 <= j < |a| ==> /*a !in f.reads(j,a[j]) &&*/ f.requires(j,a[j])
//   modifies a
  ensures |a| == |a'|
  ensures forall j :: 0 <= j < |a| ==> a'[j] == f(j,old(a[j]))
{
  var i := 0;
  a' := a;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |a| == |a'|
    invariant forall j :: i <= j < |a| ==> a'[j] == old(a[j])
    invariant forall j :: 0 <= j < i ==> a'[j] == f(j,old(a[j]))
  {
    a' := a'[i := f(i,a[i])];
    i := i + 1;
  }
}

// here's yet another version
// forall statement cannot update a variable declared outside it
method VectorUpdate''<A>(a : array<A>, f : (int,A) ~> A)
  requires forall j :: 0 <= j < a.Length ==> a !in f.reads(j,a[j]) && f.requires(j,a[j])
  modifies a
  ensures forall j :: 0 <= j < a.Length ==> a[j] == f(j,old(a[j]))
{
  forall i | 0 <= i < a.Length {
    a[i] := f(i,a[i]);
  }
}

method Main()
{
  if (*)
  {
    var v := seq(10, _ => 0);
    // Hey, works as an initialiser:
    var v' := VectorUpdate(10, v, (i,_) => i);
    assert |v'| == |v|;
    // PrintSeq(v');
    var v'' := VectorUpdate(10, v', (_,x) => x + 1);
    // PrintSeq(v');
    // Phew, now they are all positive, so we can do:
    var v''' := VectorUpdate(10, v'', (_,x) requires x != 0 => 100 / x);
    // PrintSeq(v''');
    var u := seq(10, _ => 0);
    // Hey, works as a copy as well!
    var u' := VectorUpdate(10, u, (i,_) requires 0 <= i < 10 /*reads v*/ => v'''[i]);
    // PrintSeq(u');
    // Having some fun with the index:
    var z := seq(9, _ => 0);
    var z' := VectorUpdate(9, z, (i,_) requires 0 <= i < 9 /*reads u*/ => u'[i] + u'[i+1]);
    // PrintSeq(z');
    assert z'[8] == 21; // voila, the prover also knows what's going on
  }
  else
  {
    var v := seq(10, _ => 0);
    // Hey, works as an initialiser:
    var v' := VectorUpdate(10, v, (i,_) => i);
    assert |v'| == |v|;
    // PrintSeq(v');
    var v'' := VectorUpdate(10, v', (_,x) => x + 1);
    // PrintSeq(v');
    // Phew, now they are all positive, so we can do:
    var v''' := VectorUpdate(10, v'', (_,x) requires x != 0 => 100 / x);
    // PrintSeq(v''');
    var u := seq(10, _ => 0);
    // Hey, works as a copy as well!
    var u' := VectorUpdate(10, u, (i,_) requires 0 <= i < 10 /*reads v*/ => v'''[i]);
    // PrintSeq(u');
    // Having some fun with the index:
    var z := seq(9, _ => 0);
    var z' := VectorUpdate(9, z, (i,_) requires 0 <= i < 9 /*reads u*/ => u'[i] + u'[i+1]);
    // PrintSeq(z');
    assert z'[8] == 21; // voila, the prover also knows what's going on
  }
}

method PrintSeq(a : seq<int>)
{
  var i := 0;
  while i < |a| {
    if i != 0 {
	  print ", ";
	}
    print a[i];
    i := i + 1;
  }
  print "\n";
}
