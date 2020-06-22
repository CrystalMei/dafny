// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// this is a rather verbose version of the VectorUpdate method
datatype AbInt = Z | S(AbInt) | Some
function method Leq (e1: AbInt, e2: AbInt) : (b: bool)
  ensures forall x, y, z :: Leq (x, y) && Leq(y, z) ==> Leq(x, z)

function method Lt (e1: AbInt, e2: AbInt) : (b: bool)
  ensures forall x, y, z :: Lt (x, y) && Lt(y, z) ==> Lt(x, z)

function method Add (n: AbInt, m: AbInt) : (r: AbInt)
  ensures forall x, y :: Add(x, y) == Add(y, x)
// {
  // match n
  // case Z => m
  // case S(n') => S(Add(n', m)) 
// }

function method Mul (n: AbInt, m: AbInt) : (r: AbInt)
  ensures n == Z ==> r == Z
  ensures m == Z ==> r == Z
// {
  // match n
  // case Z => Z
  // case S(n') => Add(m, Mul(n', m)) 
// }

function method Div (n: AbInt, m: AbInt) : (r: AbInt)
  requires m != Z
  ensures Mul(m, r) == n

method VectorUpdate<A>(N: int, a : seq<A>, f : (int,A) ~> A) returns (a': seq<A>)
  requires N == |a|
  requires forall j :: 0 <= j < N ==> f.requires(j,a[j])
//   requires forall j :: 0 <= j < N ==> a !in f.reads(j,a[j])
//   modifies a
  ensures |a| == |a'|
  ensures forall j :: 0 <= j < N ==> a'[j] == f(j,a[j])
{
  var i := 0;
  a' := a;
  while i < N
    invariant 0 <= i <= N
    invariant |a| == |a'|
    invariant forall j :: i <= j < N ==> f.requires(j,a'[j])
    invariant forall j :: 0 <= j < N ==> f.requires(j,a[j])
    // invariant forall j :: i <= j < N ==> a !in f.reads(j,a[j])
    invariant forall j :: i <= j < N ==> a'[j] == a[j]
    invariant forall j :: 0 <= j < i ==> a'[j] == f(j,a[j])
  {
    a' := a'[i := f(i,a[i])];
    i := i + 1;
  }
}

// function method int2adt (n: int) : (AbInt)
//   // decreases n
// {
//   if n == 0 then Z
//   else S(int2adt(n - 1))
// }

method Main()
{
  if (*)
  {
    // v = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    var v := seq(10, _ => Z);
    // Hey, works as an initialiser:
    // v' = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    var v' := VectorUpdate(10, v, (i,_) => Some);
    assert |v'| == |v|;
    // PrintSeq(v');
    // v' = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    v' := VectorUpdate(10, v', (_,x) => S(x));
    // PrintSeq(v');
    // Phew, now they are all positive, so we can do:
    // v' = [100, 50, 33, 25, 20, 16, 14, 12, 11, 10]
    v' := VectorUpdate(10, v', (_,x) requires x != Z => Div(Some, x));
    // PrintSeq(v');

    // u = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    var u := seq(10, _ => Z);
    // Hey, works as a copy as well!
    // u' = [100, 50, 33, 25, 20, 16, 14, 12, 11, 10]
    var u' := VectorUpdate(10, u, (i,_) requires 0 <= i < 10 => v'[i]);
    // PrintSeq(u');

    // Having some fun with the index:
    // z = [0, 0, 0, 0, 0, 0, 0, 0, 0]
    var z := seq(9, _ => Z);
    // z' = [150, 83, 58, 45, 35, 30, 26, 23, 21]
    var z' := VectorUpdate(9, z, (i,_) requires 0 <= i < 9 => Add(u'[i], u'[i+1]));
    // PrintSeq(z');

    assert z'[8] == Some; // voila, the prover also knows what's going on
  }
  else
  {
    // v = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    var v := seq(10, _ => Z);
    // Hey, works as an initialiser:
    // v' = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    var v' := VectorUpdate(10, v, (i,_) => Some);
    assert |v'| == |v|;
    // PrintSeq(v');
    // v' = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    v' := VectorUpdate(10, v', (_,x) => S(x));
    // PrintSeq(v');
    // Phew, now they are all positive, so we can do:
    // v' = [100, 50, 33, 25, 20, 16, 14, 12, 11, 10]
    v' := VectorUpdate(10, v', (_,x) requires x != Z => Div(Some, x));
    // PrintSeq(v');

    // u = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    var u := seq(10, _ => Z);
    // Hey, works as a copy as well!
    // u' = [100, 50, 33, 25, 20, 16, 14, 12, 11, 10]
    var u' := VectorUpdate(10, u, (i,_) requires 0 <= i < 10 => v'[i]);
    // PrintSeq(u');

    // Having some fun with the index:
    // z = [0, 0, 0, 0, 0, 0, 0, 0, 0]
    var z := seq(9, _ => Z);
    // z' = [150, 83, 58, 45, 35, 30, 26, 23, 21]
    var z' := VectorUpdate(9, z, (i,_) requires 0 <= i < 9 => Add(u'[i], u'[i+1]));
    // PrintSeq(z');

    assert z'[8] == Some; // voila, the prover also knows what's going on
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
