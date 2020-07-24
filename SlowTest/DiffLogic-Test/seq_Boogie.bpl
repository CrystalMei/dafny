// procedure S1(len: int) returns (a: [int]bool);
//   requires 0 < len;
//   ensures (forall j: int :: 0 <= j && j < len ==> a[j]);

// implementation S1(len: int) returns (a: [int]bool)
// {
//     var i: int;
//     i := 0;
//     a[0] := true;
//     while ( i < len )
//         invariant 0 <= i && i <= len;
//         invariant (forall j: int :: 0 <= j && j < i ==> a[j]);
//     {
//         a[i] := true;
//         assume (forall j: int :: i == j ==> a[j]);
//         i := i + 1;
//     }
// }

procedure S2(in: [int]int, len: int) returns (out: [int]int);
  requires in[0] == 0 && (forall i: int :: 0 <= i && i < len - 1 ==> in[i + 1] == in[i] + 1); // this `requires` works
//   requires in[0] == 0 && (forall i: int :: 0 <= i ==> in[i + 1] == in[i] + 1); // this `requires` makes verification run forever
  requires 0 < len;
  ensures (forall j: int :: 0 <= j && j < len ==> out[j] == in[j]);

implementation S2(in: [int]int, len: int) returns (out: [int]int)
{
    var i : int;

    i := 0;
    out[i] := 0;
    while (i < len)
      invariant 0 <= i && i <= len;
      invariant out[0] == 0 && (forall j: int :: 0 <= j && j < i ==> out[j] == in[j]);
    {
        out[i] := in[i];
        assume (forall j: int :: i == j ==> out[j] == in[j]);
        i := i + 1;
    }

    i := 0;
    while (i < len)
      invariant 0 <= i && i <= len;
      invariant (forall j: int :: 0 <= j && j < i ==> out[j] == in[j]);
    {
        i := i + 1;
    }
}