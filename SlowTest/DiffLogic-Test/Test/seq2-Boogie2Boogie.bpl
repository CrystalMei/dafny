// Boogie program verifier version 2.4.1.10503, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: seq2_Boogie.bpl /trace /proverOpt:O:smt.arith.solver=3 /proverOpt:LOGIC=DLA /print:seq2-Boogie2Boogie.bpl /proverLog:seq2-Boogie2z3.smt2

function add(x: int, y: int) : int;

axiom (forall x: int, y: int :: { add(x, y): int } add(x, y): int == x + y);

procedure bound(i: int, j: int, l: int, h: int);
  ensures i >= l && j >= l ==> l + l <= add(i, j);
  ensures i < h && j < h ==> add(i, j) < h + h;



procedure bound2(l: int, h: int);
  ensures (forall i: int, j: int :: i >= l && j >= l ==> l + l < add(i, j));
  ensures (forall i: int, j: int :: i < h && j < h ==> add(i, j) < h + h);



procedure P(i: int, j: int, l: int);
  requires l > 10;



implementation P(i: int, j: int, l: int)
{
    call bound2(0, 5);
    if (0 <= i && i < j && j < 5)
    {
        assert 0 <= add(i, j);
        assert add(i, j) < l;
    }
}


