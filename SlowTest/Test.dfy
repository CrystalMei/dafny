include "A-Test-Module.dfy"

import opened A`Basic

method Test (i: AbInt, j: AbInt, s: AbSeq<AbInt>)
{
    assume AbLeq(I0, i);
    assume AbLeq(j, AbSeqLen(s));
    assume AbLeq(i, j);
    var s' := AbSeqSlice(i, j, s);
    assert AbSeqLen(s') == AbSub(j, i);
    assert
        (forall x :: AbLeq(i, x) && AbLt(x, j) ==>
            // precond begins
            AbLeq(I0, x) ==> AbLt(x, AbSeqLen(s)) ==>
            AbLeq(I0, AbSub(x, i)) ==> AbLt(AbSub(x, i), AbSeqLen(s')) ==>
            // precond ends
            AbSeqIndex(x, s) == AbSeqIndex(AbSub(x, i), s') // s[i..j] w/ s[i] and w/o s[j]
        );
}