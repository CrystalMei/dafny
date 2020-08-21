
lemma P1_lemma_instance(i: int, j: int, k: int)
    requires k > 0
    ensures i < j ==> k * i < k * j
    // { assume i < j ==> k * i < k * j; } // an assume statement cannot be compiled

lemma P1_lemma_forall()
    ensures forall i: int, j: int, k: int:: i < j && k > 0 ==> k * i < k * j
    // { assume forall i: int, j: int, k: int:: i < j && k > 0 ==> k * i < k * j; } // an assume statement cannot be compiled

method P1 ()
// (smt.diff_logic: non-diff logic expression (* (LitInt 2) |x#0@0|))
// unknown
{
    var x: int;
    var y: int;

    // turn this on, precond error and assert error
    P1_lemma_instance (x, y, 2);

    // turn this on, verified with error (method has no body)
    // P1_lemma_forall();
    assert (x < y ==> 2 * x < 2 * y);
    // assert (2 * x <= 2 * y ==> 3 * x <= 3 * y);
}

method P3 ()
// (smt.diff_logic: non-diff logic expression (* |x#0@0| |y#0@0|))
// unknown
{
    var x: int;
    var y: int;
    // assume (forall i: int, j: int, k: int :: 0 < i * j && i * j < k ==> i < k && j < k); // no trigger found
    assume (forall i: int, j: int :: 0 < i * j && i * j < 10 ==> i < 10 && j < 10); // work
    assert (0 < x * y && x * y < 10 ==> x < 10); // assertion violation
}

lemma P5_lemma_forall()
    ensures forall i1: int, i2: int, j: int :: i1 + i2 > j && i2 > 0 ==> (i1 + i2 + i2) > j

lemma P5_lemma_instance(i1: int, i2: int, j: int)
    ensures i1 + i2 > j && i2 > 0 ==> (i1 + i2 + i2) > j

method P5 ()
// (smt.diff_logic: non-diff logic expression (+ |x#0@0| (* 2 |y#0@0|)))
// unknown
{
    var x : int;
    var y : int;
    // assume forall i1: int, i2: int, j1: int, j2: int :: i1 > j1 && i2 > j2 ==> (i1 + i2) > (j1 + j2); // doesn't work
    // P5_lemma_forall (); // doesn't work
    P5_lemma_instance(x, y, 10); // doesn't work
    // assume forall i1: int, i2: int {:trigger (i1 + i2)} :: i1 + i2 > 10 && i2 > 0 ==> i1 + i2 + i2 > 10; // work
    // assert (x + y > 10 && y > 0 ==> x + y + y > 10);
    assert (x + y > 10 && y > 0 ==> x + y + y > 9); // assertion violation
}

method P6 ()
// (smt.diff_logic: non-diff logic expression (* (LitInt 4) |y#0@0|))
// unknown
{
    var x : int;
    var y : int;
    // assume forall i: int, j : int, k: int :: i == j ==> k * i == k * j;
    assert (x == y ==> 3 * x == 3 * y);

    assume forall i: int, j: int, k: int :: i < j && k > 0 ==> k * i < k * j;
    assert (x < y ==> 3 * x < 3 * y);
    assert (0 <= x && 0 <= y && x <= y ==> 3 * x <= 3 * y);

    assume forall i: int, j: int {:trigger (i + j)} :: j >= 0 ==> i <= i + j;
    assume forall i: int :: 4 * i == (3 * i) + i;
    assert (0 <= y ==> 3 * y <= (3 * y) + y);
    // assert (0 <= y ==> 3 * y <= 4 * y); // doesn't work
    assert (0 <= y && 3 * x <= 3 * y ==> 3 * x <= (3 * y) + y);  // doesn't work
    assert (0 <= x && 0 <= y && x <= y ==> 3 * x <= (3 * y) + y);  // doesn't work
    assert (0 <= x && 0 <= y && 2 * x <= 2 * y ==> 3 * x <= 4 * y); // assertion violation
}