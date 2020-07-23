method S(a: seq<bool>)
{
    var a: seq<bool>;
    var len: int := |a|;
    var i: int := 0;
    while ( i < len )
        invariant |a| == len
        invariant 0 <= i <= |a|
        invariant forall j :: 0 <= j < i ==> a[j]
        decreases len - i
    {
        a := a[i := true];
        i := i + 1;
    }
    assert (forall j: int :: 0 <= j < len ==> a[j]);
}