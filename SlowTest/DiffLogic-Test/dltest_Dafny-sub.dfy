
lemma P1_lemma_instance(i: int, j: int, k: int)
    requires k > 0
    ensures i < j ==> k * i < k * j
    { assume i < j ==> k * i < k * j; } // an assume statement cannot be compiled

lemma P1_lemma_forall()
    ensures forall i: int, j: int, k: int:: i < j && k > 0 ==> k * i < k * j
    { assume forall i: int, j: int, k: int:: i < j && k > 0 ==> k * i < k * j; } // an assume statement cannot be compiled

method P1 ()
// (smt.diff_logic: non-diff logic expression (* (LitInt 2) |x#0@0|))
// unknown
{
    var x: int;
    var y: int;

    // turn this on, precond error and assert error
    // P1_lemma_instance (x, y, 2);

    // turn this on, verified with error (method has no body)
    P1_lemma_forall();
    assert (x < y ==> 2 * x < 2 * y);
    // assert (2 * x <= 2 * y ==> 3 * x <= 3 * y);
}
