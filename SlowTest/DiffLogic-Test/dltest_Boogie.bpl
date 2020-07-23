procedure P1 ()
// unsat
{
    var x : int;
    var y : int;
    assert (x < y ==> 2 * x < 2 * y);
    assert (2 * x <= 2 * y ==> 3 * x <= 3 * y);
}

procedure P2 ()
// unsat
{
    var x : int;
    var y : int;
    assert (x * y == y * x);
}

procedure P3 ()
// (smt.diff_logic: non-diff logic expression (* x y))
// (smt.diff_logic: non-diff logic expression (* x y))
// unknown
{
    var x : int;
    var y : int;
    assume (forall i: int, j: int :: 0 < i * j && i * j < 10 ==> i < 10 && j < 10); // cannot do `forall k :: i * j < k`
    assert (0 < x * y && x * y < 10 ==> x < 10);
}

procedure P4 ()
// unsat
{
    var x : int;
    var y : int;
    assert (y >= 0 && x - y > 0 ==> x > 0);
}

procedure P5 ()
// (smt.diff_logic: non-diff logic expression (+ x (* 2 y)))
// (smt.diff_logic: non-diff logic expression (+ x (* 2 y)))
// unknown
{
    var x : int;
    var y : int;
    // assume (forall i: int, j: int :: {(i + j)} j > 0 ==> i < i + j);
    // assert (y > 0 ==> x + y + y > x + y);
    assume (forall i1: int, i2: int :: {(i1 + i2)} i1 + i2 > 10 && i2 > 0 ==> i1 + i2 + i2 > 10);
    assert (x + y > 10 && y > 0 ==> x + y + y > 9);
}


procedure P6 ()
// (smt.diff_logic: non-diff logic expression (+ (* 3 x) (* (- 4) y)))
// (smt.diff_logic: non-diff logic expression (+ (* 3 x) (* (- 4) y)))
// unknown
{
    var x : int;
    var y : int;
    // assert (forall i: int, j: int, k: int :: i <= j && j <= k ==> i <= k);
    assert (2 * x <= 2 * y ==> 3 * x <= 3 * y);
    assert (forall i: int, j: int :: {(i + j)} 0 <= j ==> i <= i + j);
    assert (0 <= y ==> 3 * y <= 4 * y);
    assert (3 * x <= 3 * y && 3 * y <= 4 * y ==> 3 * x <= 4 * y); // error
    assert (3 * x <= 3 * y && 0 <= y ==> 3 * x <= 4 * y); // error
    assert (0 <= x && 0 <= y && 2 * x <= 2 * y ==> 3 * x <= 4 * y); // error
}

procedure P7 ()
// (smt.diff_logic: non-diff logic expression (* x y))
// unsat
{
    var x : int;
    var y : int;
    var z : int;
    assert (0 <= x * y && x * y + 10 <= z ==> 0 <= z);
}