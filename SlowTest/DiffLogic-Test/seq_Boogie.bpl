type Val;
procedure S0() returns (a: [Val]bool) // works
{
    var X: Val;
    a[X] := true;
    // assume a[X];
    assert (forall j: Val :: j == X ==> a[j]);
}

procedure S0'() returns (a: [int]bool)
{
    a[0] := true;
    // assume a[X];
    assert (forall j:int :: j == 0 ==> a[j]); // quantifier tactic?
}

// procedure S1(len: int) returns (a: [int]bool)
//   requires 0 < len;
//   ensures (forall j: int :: 0 <= j && j < len ==> a[j]);
// {
//     var i: int;
//     i := 0;
//     a[0] := true;
//     while ( i < len )
//         invariant 0 <= i && i <= len;
//         invariant (forall j: int :: {a[j]} 0 <= j && j < i ==> a[j]);
//     {
//         a[i] := true;
//         // assume a[i]; // not work
//         // assert (forall j: int :: 0 <= j && j < i ==> a[j]);
//         // assume (forall j: int :: {a[j]} i == j ==> a[j]);

//         // assert (forall j: int :: i == j ==> 0 <= j && j < i + 1 ==> a[j]);
//         // assert (forall j: int :: i != j ==> 0 <= j && j < i + 1 ==> a[j]);

//         // assert (0 <= i && i < i + 1 ==> a[i]);

//         i := i + 1;
//     }
// }

// procedure S2(in: [int]int, len: int) returns (out: [int]int)
// //   requires in[0] == 0 && (forall i: int :: 0 <= i && i < len - 1 ==> in[i + 1] == in[i] + 1); // works
// //   requires in[0] == 0 && (forall i: int :: 0 <= i ==> in[i] == 1); // works
//   requires in[0] == 0 && (forall i: int :: {in[i] + 1} 0 <= i ==> in[i + 1] == in[i] + 1); // need trigger to work
//   requires 0 < len;
//   ensures (forall j: int :: 0 <= j && j < len ==> out[j] == in[j]);
// {
//     var i : int;

//     i := 0;
//     out[i] := 0;
//     while (i < len)
//       invariant 0 <= i && i <= len;
//       invariant out[0] == 0 && (forall j: int :: 0 <= j && j < i ==> out[j] == in[j]);
//     {
//         out[i] := in[i];
//         // assume (forall j: int :: i == j ==> out[j] == in[j]);
//         i := i + 1;
//     }

//     i := 0;
//     while (i < len)
//       invariant 0 <= i && i <= len;
//       invariant (forall j: int :: 0 <= j && j < i ==> out[j] == in[j]);
//     {
//         i := i + 1;
//     }
// }