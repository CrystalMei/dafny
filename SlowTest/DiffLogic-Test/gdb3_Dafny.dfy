
function method Add(a: int, b: int): int { a + b }
function method Sub(a: int, b: int): int { a - b }

method test<X> (s: seq<X>) returns (s': seq<X>)
    {
        // assume |s| - 1 == |s'|;
        assume |s| == |s'| + 1;
        assert forall i : int :: 0 <= i < |s'| ==> 0 <= i + 1;
        assert forall i : int :: 0 <= i < |s'| ==> i + 1 < |s|;
        // assert forall i : int :: 0 <= i < |s'| ==> s'[i] == s[Add(i, 1)];
    }

predicate myP(a: bool, b: bool)
{
  a || b
}
method myTest2 (a: bool, b: bool)
    { if myP(a, b) { assert a || b; } } // big problem