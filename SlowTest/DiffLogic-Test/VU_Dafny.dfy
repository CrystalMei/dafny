// VectorUpdate-seq.dfy

function method Dec(a: int, b: int) : int
lemma Props_dec_one (sum: int)
    ensures forall j :: Dec(sum, j + 1) < Dec(sum, j)
lemma Props_dec_lower_bound (sum: int, x: int)
    requires x <= sum
    ensures 0 <= Dec(sum, x)

function method Div(a: int, b: int): (c: int)
    requires b != 0
    ensures a == 100 && b == 9 ==> c == 11
    ensures a == 100 && b == 10 ==> c == 10
    { a / b }

function method Add(a: int, b: int): (c: int)
    ensures a == 11 && b == 10 ==> c == 21
    { assert 11 + 10 == 21;
      assert a == 11 && b == 10 ==> a + b == 21; // failed
      a + b }

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
    invariant forall j :: i <= j < N ==> f.requires(j,a[j])
    invariant forall j :: 0 <= j < N ==> f.requires(j,a[j])
    invariant forall j :: i <= j < N ==> a'[j] == a[j]
    invariant forall j :: 0 <= j < i ==> a'[j] == f(j,a[j])
    decreases Dec(N, i)
  {
    a' := a'[i := f(i,a[i])];
    Props_dec_one (N);
    Props_dec_lower_bound(N, i);
    i := i + 1;
  }
}

function method SeqInit<X> (len: int, func : int --> X) : (s: seq<X>)
  requires len >= 0
  requires forall i : int :: 0 <= i < len ==> func.requires(i)
  ensures |s| == len
  ensures forall i : int :: 0 <= i < len ==> s[i] == func(i)

method Main()
{
  // v = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  var v := SeqInit(10, _ => 0);
  // v' = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  var v' := VectorUpdate(10, v, (i,_) => i);
  assert |v'| == |v|;
  PrintSeq(v');
  // v' = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  v' := VectorUpdate(10, v', (_,x) => x + 1);
  PrintSeq(v');
  // v' = [100, 50, 33, 25, 20, 16, 14, 12, 11, 10]
  v' := VectorUpdate(10, v', (_,x) requires x != 0 => Div(100, x));
  PrintSeq(v');

  // u = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  var u := SeqInit(10, _ => 0);
  // u' = [100, 50, 33, 25, 20, 16, 14, 12, 11, 10]
  u := VectorUpdate(10, u, (i,_) requires 0 <= i < 10 => v'[i]);
  PrintSeq(u);
  
  // z = [0, 0, 0, 0, 0, 0, 0, 0, 0]
  var z := SeqInit(9, _ => 0);
  // z' = [150, 83, 58, 45, 35, 30, 26, 23, 21]
//   z := VectorUpdate(9, z, (i,_) requires 0 <= i < 9 => u[i] + u[i+1]);
  z := VectorUpdate(9, z, (i,_) requires 0 <= i < 9 => Add(u[i], u[i+1]));
  PrintSeq(z);
  assert z[8] == 21;
}

method PrintSeq(a : seq<int>)
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
