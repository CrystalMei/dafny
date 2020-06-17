// RUN: %dafny /compile:0 /arith:2 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// z3 with trace=true & proof=true
lemma INDUCTION_EVEN_ODD(P: (nat, nat) -> bool, a: nat, b: nat)
  requires P(0, 0)
  requires forall a: nat, b: nat :: P(a, b) ==> P(2*a, 2*b)
  requires forall a: nat, b: nat :: P(a, b) ==> P(2*a, 2*b + 1)
  requires forall a: nat, b: nat :: P(a, b) ==> P(2*a + 1, 2*b)
  requires forall a: nat, b: nat :: P(a, b) ==> P(2*a + 1, 2*b + 1)
  ensures P(a, b)
{
  if a == 0 && b == 0 {
  } else {
    INDUCTION_EVEN_ODD(P, a / 2, b / 2);
  }
}