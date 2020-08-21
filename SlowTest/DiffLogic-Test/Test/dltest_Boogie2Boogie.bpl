// Boogie program verifier version 2.4.1.10503, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: dltest_Boogie.bpl /print:dltest_Boogie2Boogie.bpl /proverLog:dltest_Boogie2z3.smt2

procedure P1();



implementation P1()
{
  var x: int;
  var y: int;

    assert x < y ==> 2 * x < 2 * y;
    assert 2 * x <= 2 * y ==> 3 * x <= 3 * y;
}



procedure P2();



implementation P2()
{
  var x: int;
  var y: int;

    assert x * y == y * x;
}



procedure P3();



implementation P3()
{
  var x: int;
  var y: int;

    assert 0 < x * y && x * y < 10 ==> x < 10;
}



procedure P4();



implementation P4()
{
  var x: int;
  var y: int;

    assert y >= 0 && x - y > 0 ==> x > 0;
}



procedure P5();



implementation P5()
{
  var x: int;
  var y: int;

    assert x + y > 10 && y > 0 ==> x + y + y > 9;
}


