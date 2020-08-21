
function method Dec(a: int, b: int) : int
lemma Props_dec (sum: int, a: int, b: int)
    requires a > b
    ensures Dec(sum, a) < Dec(sum, b)

lemma Props_dec_one (sum: int)
    ensures forall j :: Dec(sum, j + 1) < Dec(sum, j)

lemma Props_dec_lower_bound (sum: int, x: int)
    requires x <= sum
    ensures 0 <= Dec(sum, x)

method S1()
{
    var a: seq<bool>;
    var len: int := |a|;
    var i: int := 0;
    while ( i < len )
        invariant |a| == len
        invariant 0 <= i <= len
        invariant forall j :: 0 <= j < i ==> a[j]
        decreases Dec(len, i)
    {
        a := a[i := true];
        // Props_dec(len, i + 1, i); // Error: decreases expression might not decrease
        Props_dec_one (len); // works
        Props_dec_lower_bound(len, i);
        i := i + 1;
    }
    assert (forall j: int :: 0 <= j < len ==> a[j]);
}