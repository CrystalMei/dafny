// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint.dfy" "%s" > "%t"
// RUN: %dafny /noVerify /compile:0 "%t.dprint.dfy" >> "%t"
// RUN: %diff "%s.expect" "%t"

function method Fib(n: nat): nat
{
  if n < 2 then n else Fib(n-1) + Fib(n-2)
}

// ~2.6s
method M3(a: array<int>) returns (r: int)
  requires forall i :: 0 <= i < a.Length ==> a[i] == 6;
  ensures (r + var t := r; t*2) == 3*r;
{
  assert Fib(2) + Fib(4) == Fib(0) + Fib(1) + Fib(2) + Fib(3);

  {
    var x,y := Fib(8), Fib(11);
    assume x == 21;
    // assert Fib(7) == 3 ==> Fib(9) == 24; // comment out 1
    assume Fib(1000) == 1000;
    assume Fib(9) - Fib(8) == 13;
    // assert Fib(9) <= Fib(10); // comment out 2; (1 + 2) can make 2.6s -> 1.1s
    assert y == 89;
  }

  assert Fib(1000) == 1000;

  // comment out the following, 2.6s -> 5.2s?
  forall i | 0 <= i < a.Length ensures true; {
    var j := i+1;
    assert j < a.Length ==> a[i] == a[j]; // only comment out this, won't change much
  }
  // assert forall i :: 0 <= i < a.Length ==> var j := i+1; j < a.Length ==> a[i] == a[j];
}

// ~ 2.6s
method M4(a: array<int>) returns (r: int)
  requires forall i :: 0 <= i < a.Length ==> a[i] == 6;
  ensures (r + var t := r; t*2) == 3*r;
{
  // assert Fib(2) + Fib(4) == Fib(0) + Fib(1) + Fib(2) + Fib(3);
  assert
    var x,y := Fib(8), Fib(11);
    assume x == 21;
    assert Fib(7) == 3 ==> Fib(9) == 24;
    assume Fib(1000) == 1000;
    assume Fib(9) - Fib(8) == 13;
    // assert Fib(9) <= Fib(10); // comment out this, 2.6s -> 1.3s
    y == 89;
  assert Fib(1000) == 1000;
  assert forall i :: 0 <= i < a.Length ==> var j := i+1; j < a.Length ==> a[i] == a[j];
}
