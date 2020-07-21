procedure P1 ()
{
    var x : int;
    var y : int;
    assert (x < y ==> 2 * x < 2 * y); // (error "line 38 column 1: logic only supports difference arithmetic")
    assert (2 * x <= 2 * y ==> 3 * x <= 3 * y);
}

procedure P2 ()
{
    var x : int;
    var y : int;
    assert (x * y == y * x); // (error "line 80 column 1: logic does not support nonlinear arithmetic")
}

procedure P3 () // non-diff logic expression (* x y)
// unknown - (tactic-exception "smt tactic failed to show goal to be sat/unsat (incomplete (theory difference-logic))")
{
    var x : int;
    var y : int;
    assert (0 < x * y && x * y < 10 ==> x < 10); // (error "line 122 column 1: logic does not support nonlinear arithmetic")
}

procedure P4 ()
{
    var x : int;
    var y : int;
    assert (y >= 0 && x - y > 0 ==> x > 0);
}

procedure P5 () // non-diff logic expression (+ x y)
{
    var x : int;
    var y : int;
    assert (x + y > 10 && y > 0 ==> x + y + y > 9); // (error "line 206 column 1: logic only supports difference arithmetic")
}