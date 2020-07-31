// GDB test for generic type axiom

type t;
axiom (forall x: t :: true);
procedure P (a: int, b: int)
    { assert (a == 10 && b == 11 ==> a + b == 21); }