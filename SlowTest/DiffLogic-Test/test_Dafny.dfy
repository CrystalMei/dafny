method myAdd(a: int, b: int)
    { assert a == 10 && b == 11 ==> a + b == 21; }

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