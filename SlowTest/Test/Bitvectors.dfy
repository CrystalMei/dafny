// RUN: %dafny /compile:3 /print:"%t.print" /rprint:- /env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ~ 12s
method Unary_All(x: bv16) returns (y: bv16)
  ensures y == x - 2
{
  y := -(-!-!!--(x));
  y := !-y;
  var F := 0xffff;
  calc {
    y;
    !--(-!-!!--(x));
    F - ---!-!!--x;
    { assert ---!-!!--x == -!-!!--x; }
    F - -!-!!--x;
    F + !-!!--x;
    F + F - -!!--x;
    F + F + !!--x;
    { assert !!--x == --x == x; }
    F + F + x;
    x - 2;
  }
}

// ~ 0.05s - pure logical expression is quick
method Unary_1(x: bv16) returns (y: bv16)
  ensures y == x - 2
{
  y := -(-!-!!--(x));
  y := !-y;
  var F := 0xffff;
  calc {
    y;
    !--(-!-!!--(x));
  }
}

// ~ 9s
method Unary_2(x: bv16) returns (y: bv16)
  ensures y == x - 2
{
  y := -(-!-!!--(x));
  y := !-y;
  var F := 0xffff;
  calc {
    y;
    F - ---!-!!--x;
  }
}

// ~ 9.3s
method Unary_3(x: bv16) returns (y: bv16)
  ensures y == x - 2
{
  y := -(-!-!!--(x));
  y := !-y;
  var F := 0xffff;
  calc {
    y;
    F - -!-!!--x;
  }
}

// ~ 8.7s
method Unary_4(x: bv16) returns (y: bv16)
  ensures y == x - 2
{
  y := -(-!-!!--(x));
  y := !-y;
  var F := 0xffff;
  calc {
    y;
    F + !-!!--x;
  }
}

// ~ 8.8s
method Unary_5(x: bv16) returns (y: bv16)
  ensures y == x - 2
{
  y := -(-!-!!--(x));
  y := !-y;
  var F := 0xffff;
  calc {
    y;
    F + F - -!!--x;
  }
}

// ~ 8.7s
method Unary_6(x: bv16) returns (y: bv16)
  ensures y == x - 2
{
  y := -(-!-!!--(x));
  y := !-y;
  var F := 0xffff;
  calc {
    y;
    F + F + !!--x;
  }
}

// ~ 8.8s
method Unary_7(x: bv16) returns (y: bv16)
  ensures y == x - 2
{
  y := -(-!-!!--(x));
  y := !-y;
  var F := 0xffff;
  calc {
    y;
    F + F + x;
  }
}

// ~ 0.04s - without 0xffff is quick
method Unary_8(x: bv16) returns (y: bv16)
  ensures y == x - 2
{
  y := -(-!-!!--(x));
  y := !-y;
  var F := 0xffff;
  calc {
    y;
    x - 2;
  }
}

// ~ 8.9s
method Unary_2_2(x: bv16) returns (y: bv16)
  ensures y == x - 2
{
  y := -(-!-!!--(x));
  y := !-y;
  var F := 0xffff;
  calc {
    y;
    F - ---!-!!--x;
    x - 2;
  }
}

// ~ 8.8s
method Unary_3_2(x: bv16) returns (y: bv16)
  ensures y == x - 2
{
  y := -(-!-!!--(x));
  y := !-y;
  var F := 0xffff;
  calc {
    y;
    F - -!-!!--x;
    x - 2;
  }
}
// ~ 8.8s 
method Unary_4_2(x: bv16) returns (y: bv16)
  ensures y == x - 2
{
  y := -(-!-!!--(x));
  y := !-y;
  var F := 0xffff;
  calc {
    y;
    F + !-!!--x;
    x - 2;
  }
}

// ~ 4s
method Unary_5_2(x: bv16) returns (y: bv16)
  ensures y == x - 2
{
  y := -(-!-!!--(x));
  y := !-y;
  var F := 0xffff;
  calc {
    y;
    F + F - -!!--x;
    x - 2;
  }
}

// ~ 4s
method Unary_6_2(x: bv16) returns (y: bv16)
  ensures y == x - 2
{
  y := -(-!-!!--(x));
  y := !-y;
  var F := 0xffff;
  calc {
    y;
    F + F + !!--x;
    x - 2;
  }
}

// ~ 4s
method Unary_7_2(x: bv16) returns (y: bv16)
  ensures y == x - 2
{
  y := -(-!-!!--(x));
  y := !-y;
  var F := 0xffff;
  calc {
    y;
    F + F + x;
    x - 2;
  }
}
