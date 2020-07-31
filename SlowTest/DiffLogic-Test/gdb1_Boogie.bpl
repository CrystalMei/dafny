// GDB test for sparse diff logic solver vs dense diff logic solver

// type Val;
// procedure S0() returns (a: [Val]bool) // works
// {
//     var X: Val;
//     a[X] := true;
//     // assume a[X];
//     assert (forall j: Val :: j == X ==> a[j]);
// }

procedure S0'() returns (i: int, a: [int]bool)
{
    a[0] := true;
    // assume a[X];
    assert (i == 0 ==> a[i]); // quantifier tactic?
    // assert (forall j:int :: j == 0 ==> a[j]); // quantifier tactic?
}
