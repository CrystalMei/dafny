function add(x: int, y: int) : int
    {x + y}

procedure bound(i: int, j: int, l: int, h: int);
    ensures (i >= l && j >= l ==> l + l <= add(i, j));
    ensures (i < h && j < h ==> add(i, j) < h + h);

procedure bound2(l: int, h: int);
    ensures (forall i:int, j:int :: i >= l && j >= l ==> l + l < add(i, j));
    ensures (forall i:int, j:int :: i < h && j < h ==> add(i, j) < h + h);

procedure P(i: int, j: int, l: int)
    requires l > 10;
{  
    // call bound(i, j, 0, 5);
    call bound2(0, 5);
    // assert i >= 0 && j >= 0 ==> add(i, j) >= 0;
    // assert i < 5 && j < 5 ==> add(i, j) < 10;
    // assert (forall k: int :: k < 10 ==> k < l);
    // assert add(i, j) < 10 ==> add(i, j) < l;
    if (0 <= i && i < j && j < 5)
    {
        assert 0 <= add(i, j);
        assert add(i, j) < l;
    }
}
