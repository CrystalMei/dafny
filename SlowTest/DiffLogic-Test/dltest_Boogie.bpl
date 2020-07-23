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
    assert (x + y > 10 && y > 0 ==> x + y + y > 9);
}


procedure P6 ()
// (smt.diff_logic: non-diff logic expression (+ (* 3 x) (* (- 4) y)))
// (smt.diff_logic: non-diff logic expression (+ (* 3 x) (* (- 4) y)))
// unknown
{
    var x : int;
    var y : int;
    assert (0 <= x && 0 <= y && 2 * x <= 2 * y ==> 3 * x <= 4 * y);
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