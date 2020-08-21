method P1 ()
// (smt.diff_logic: non-diff logic expression (* (LitInt 2) |x#0@0|))
// unknown
{
    var x: int;
    var y: int;

    assert (x < y ==> 2 * x < 2 * y); // assertion violation
    assert (2 * x <= 2 * y ==> 3 * x <= 3 * y); // assertion violation
}

method P2 ()
// (smt.diff_logic: non-diff logic expression (* |x#0@0| |y#0@0|))
// (smt.diff_logic: non-diff logic expression (* |x#0@0| |y#0@0|))
// unsat
{
    var x: int;
    var y: int;
    assert (x * y == y * x);
}

method P3 ()
// (smt.diff_logic: non-diff logic expression (* |x#0@0| |y#0@0|))
// unknown
{
    var x: int;
    var y: int;
    assert (0 < x * y && x * y < 10 ==> x < 10); // assertion violation
}

method P4 ()
// unsat
{
    var x: int;
    var y: int;
    assert (y >= 0 && x - y > 0 ==> x > 0);
}

method P5 ()
// (smt.diff_logic: non-diff logic expression (+ |x#0@0| (* 2 |y#0@0|)))
// unknown
{
    var x : int;
    var y : int;
    assert (x + y > 10 && y > 0 ==> x + y + y > 9); // assertion violation
}

method P6 ()
// (smt.diff_logic: non-diff logic expression (* (LitInt 4) |y#0@0|))
// unknown
{
    var x : int;
    var y : int;
    assert (0 <= x && 0 <= y && 2 * x <= 2 * y ==> 3 * x <= 4 * y); // assertion violation
}

method P7 ()
// unsat
{
    var x : int;
    var y : int;
    var z : int;
    assert (0 <= x * y && x * y + 10 <= z ==> 0 <= z);
}