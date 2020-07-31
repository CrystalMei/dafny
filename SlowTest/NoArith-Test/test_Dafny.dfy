function method mySeqIndex<X>(i: int, s: seq<X>): (v: X)
    requires 0 <= i < |s|
    ensures s[i] == v

method myTest(s1: seq<bool>, s2: seq<int>)
    { 
        assume forall i :: 0 <= i < |s2| ==> 0 < mySeqIndex(i, s2) < |s1|;
        assume forall i :: 0 <= i < |s1| ==> mySeqIndex(i, s1);        
        assert forall i :: 0 <= i < |s2| ==> 0 <= mySeqIndex(i, s2) < |s1| ==> mySeqIndex(mySeqIndex(i, s2), s1);
    }

predicate myP(a: bool, b: bool)
{
  a || b
}
method myTest2 (a: bool, b: bool)
    { if myP(a, b) { assert a || b; } } // big problem
// function method Add(a: int, b: int): int { a + b }
// function method Sub(a: int, b: int): int { a - b }

// method P (a: int, b: int)
//     { assert Add(a, b) == a + b; }

// method P1 (a: int, b: int, c: int)
//     { assert Add(a, b) <= c; }

// method P1 (s: seq<bool>)
// {
//     assume |s| > 0;
//     assume s[0] == true;
//     assert forall i :: i == 0 ==> s[i] == s[0];
//     assert forall i :: i == 0 ==> s[i];
// }