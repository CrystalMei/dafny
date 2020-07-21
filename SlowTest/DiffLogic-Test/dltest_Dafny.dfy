method Main ()
{
    var x: int;
    var y: int;

    assert (x < y ==> 2 * x < 2 * y);
    assert (x >= 0 && y >= 0 && x < y ==> 2 * x < 2 * y);
    assert ( x + y > 10);  // error

}