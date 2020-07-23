procedure S(len: int) returns (a: [int]bool);
  requires 0 < len;
  ensures (forall j: int :: 0 <= j && j < len ==> a[j]);

implementation S(len: int) returns (a: [int]bool)
{
    var i: int;
    i := 0;
    a[0] := true;
    while ( i < len )
        invariant 0 <= i && i <= len;
        invariant (forall j: int :: 0 <= j && j < i ==> a[j]);
    {
        a[i] := true;
        i := i + 1;
    }
    assert (forall j: int :: 0 <= j && j < len ==> a[j]);
}