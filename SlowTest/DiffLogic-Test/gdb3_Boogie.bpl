function Sub(x: int, y: int) : int
    { x - y }
    
// procedure S(x: int, y: int)
// {
//     assume y == x + 1;
//     // assert (forall i:int :: 0 <= i ==> 0 <= i + 1);
//     assert (forall i:int :: i < x ==> i + 1 < y);
// }

procedure test(x: int, y: int)
{
    // assert (x - 1 < x);
    assert (Sub(x, 1) < x);
}