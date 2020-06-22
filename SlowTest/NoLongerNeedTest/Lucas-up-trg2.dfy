// RUN: %dafny /compile:0 /arith:2 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// predicate Bit(k: nat, n: nat)
// {
//   if k == 0 then n % 2 == 1
//   else Bit(k-1, n / 2)
// }

// // This lemma says that bit 0 of an even number is never set.
// lemma ZeroBitOfEven(n: nat)
//   ensures !Bit(0, 2*n)
// {
//   var r := 2*n;
//   assert Bit(0, r) <==> r % 2 == 1;
// }

// // Function "BitSet" returns the set of bits in the binary representation
// // of a number.
// function BitSet(n: nat): set<nat>
// {
//   set i | 0 <= i < n && Bit(i, n)
// }

// // The following lemma shows that the "i < n" conjunct in
// // the set comprehension in "BitSet" does not restrict
// // the set any more than the conjunct "Bit(i, n)" does.
// lemma BitSize(i: nat, n: nat)
//   requires Bit(i, n)
//   ensures i < n
// {
// }

// // An easy-to-read name for the expression that checks if a number
// // is even.
// predicate EVEN(n: nat)
// {
//   n % 2 == 0
// }

// // The binomial function is defined like in the Pascal triangle.
// // "binom(a, b)" is also knows as "a choose b".
// function binom(a: nat, b: nat): nat
// {
//   if b == 0 then 1
//   else if a == 0 then 0
//   else binom(a-1, b) + binom(a-1, b-1)
// }

// // This lemma shows that the parity of "binom" is preserved if
// // div-2 is applied to both arguments, except in the case where
// // the first argument to "binom" is even and the second argument
// // is odd, in which case "binom" is always even.
// lemma Lucas_Binary(a: nat, b: nat)
//   ensures EVEN(binom(2*a, 2*b + 1))
//   ensures EVEN(binom(2*a, 2*b)) <==> EVEN(binom(a, b))
//   ensures EVEN(binom(2*a + 1, 2*b + 1)) <==> EVEN(binom(a, b))
//   ensures EVEN(binom(2*a + 1, 2*b)) <==> EVEN(binom(a, b))
// {
//   if a == 0 {
//   } else {
//     var a', b' := a - 1, b - 1;
//     assert binom(2*a, 2*b + 1) == binom(2*a' + 1, 2*b + 1) + binom(2*a' + 1, 2*b);
//     assert b != 0 ==> binom(2*a, 2*b) == binom(2*a' + 1, 2*b) + binom(2*a' + 1, 2*b' + 1);
//     assert EVEN(binom(2*a' + 1, 2*b + 1)) == EVEN(binom(a', b));
//     assert EVEN(binom(2*a' + 1, 2*b)) == EVEN(binom(a', b));
//   }
// }

// // Here is an alternative way to phrase the previous lemma.
// lemma Lucas_Binary'(a: nat, b: nat)
//   ensures binom(2*a, 2*b) % 2 == binom(a, b) % 2
//   ensures binom(2*a, 2*b + 1) % 2 == 0
//   ensures binom(2*a + 1, 2*b) % 2 == binom(a, b) % 2
//   ensures binom(2*a + 1, 2*b + 1) % 2 == binom(a, b) % 2
// {
//   if a != 0 {
//     var a', b' := a - 1, b - 1;
//     assert b != 0 ==> binom(2*a, 2*b) == binom(2*a' + 1, 2*b) + binom(2*a' + 1, 2*b' + 1);
//     assert binom(2*a' + 1, 2*b) % 2 == binom(a', b) % 2;
//     assert binom(2*a' + 1, 2*b + 1) % 2 == binom(a', b) % 2;
//   }
// }

// // "Suc(S)" returns the set constructed by incrementing
// // each number in "S" by 1. Stated differently, it is the
// // increment-by-1 (successor) function applied pointwise to the
// // set.
// function Suc(S: set<nat>): set<nat>
// {
//   set x | x in S :: x + 1
// }

// // The following lemma clearly shows the correspondence between
// // "S" and "Suc(S)".
// lemma SucElements(S: set<nat>)
//   ensures forall x :: x in S <==> (x+1) in Suc(S)
// {
// }

// // 0 is not in any set returned by "Suc".
// lemma ZeroNotInImageSuc(S: set<nat>)
//   ensures 0 !in Suc(S)
// {
// }

// lemma BitSet_Clauses(n: nat)
//   ensures BitSet(2*n) == Suc(BitSet(n))
//   ensures BitSet(2*n + 1) == {0} + Suc(BitSet(n))
// {
//   if n == 0 {
//   } else {
//     var nn := 2 * n;
//     forall x: nat {
//       calc {
//         x in BitSet(2*n);
//       ==  // def. BitSet
//         0 <= x < 2*n && Bit(x, 2*n);
//       ==  { ZeroBitOfEven(n); }
//         0 < x < 2*n && Bit(x, 2*n);
//       ==  { assert 0 < x ==> Bit(x, nn) == Bit(x-1, nn / 2); }
//         0 < x < 2*n && Bit(x-1, n);
//       ==  { if 0 < x && Bit(x-1, n) { BitSize(x-1, n); } }
//         0 <= x-1 < n && Bit(x-1, n);
//       ==  // def. BitSet
//         (x-1) in BitSet(n);
//       ==  // def. Suc
//         x in Suc(BitSet(n));
//       }
//     }
//     forall x: nat {
//       calc {
//         x in BitSet(2*n + 1);
//       ==  // def. BitSet
//         0 <= x < 2*n + 1 && Bit(x, 2*n + 1);
//       ==  { assert x == 0 ==> Bit(x, 2*n + 1); }
//         x == 0 || (0 < x < 2*n + 1 && Bit(x, 2*n + 1));
//       ==  { assert (2*n + 1) / 2 == n; }
//         x == 0 || (0 < x < 2*n + 1 && Bit(x-1, n));
//       ==  { if 0 < x && Bit(x-1, n) { BitSize(x-1, n); } }
//         x == 0 || (x-1) in BitSet(n);
//       ==
//         x == 0 || x in Suc(BitSet(n));
//       ==
//         x in {0} + Suc(BitSet(n));
//       }
//     }
//   }
// }
// predicate T<A> (x:A) {true} // This one failed
predicate T (x:nat) {true}
// z3 with trace=true & proof=true
lemma INDUCTION_EVEN_ODD(P: (nat, nat) -> bool, a: nat, b: nat)
  requires P(0, 0)
  requires forall a: nat, b: nat :: P(a, b) ==> P(2*a, 2*b)
  requires forall a: nat, b: nat :: P(a, b) ==> P(2*a, 2*b + 1)
  requires forall a: nat, b: nat :: P(a, b) ==> P(2*a + 1, 2*b)
  requires forall a: nat, b: nat {:trigger T(a), T(b)} :: T(a) && T(b) && P(a, b) ==> P(2*a + 1, 2*b + 1)
  ensures P(a, b)
{
  if a == 0 && b == 0 {
  } else {
    INDUCTION_EVEN_ODD(P, a / 2, b / 2);
    assert a - 1 <= 2 * (a / 2) <= a;
    assert b - 1 <= 2 * (b / 2) <= b;
    assert T(a / 2);
    assert T(b / 2);
  }
}

// lemma Lucas_Theorem(m: nat, n: nat)
//   ensures BitSet(m) <= BitSet(n) <==> !EVEN(binom(n, m))
// {
//   if m == 0 && n == 0 {
//   } else {
//     var m', n' := m/2, n/2;
//     if {
//       case m == 2*m' && n == 2*n' =>
//         calc {
//           !EVEN(binom(n, m));
//         ==  { Lucas_Binary(n', m'); }
//           !EVEN(binom(n', m'));
//         ==  { Lucas_Theorem(m', n'); }
//           BitSet(m') <= BitSet(n');
//         ==  { SucElements(BitSet(m')); SucElements(BitSet(n')); }
//           Suc(BitSet(m')) <= Suc(BitSet(n'));
//         ==  { BitSet_Clauses(m'); BitSet_Clauses(n'); }
//           BitSet(2*m') <= BitSet(2*n');
//         }
//       case m == 2*m' && n == 2*n' + 1 =>
//         calc {
//           !EVEN(binom(n, m));
//         ==  { Lucas_Binary(n', m'); }
//           !EVEN(binom(n', m'));
//         ==  { Lucas_Theorem(m', n'); }
//           BitSet(m') <= BitSet(n');
//         ==  { SucElements(BitSet(m')); SucElements(BitSet(n')); }
//           Suc(BitSet(m')) <= Suc(BitSet(n'));
//         ==  { ZeroNotInImageSuc(BitSet(m')); }
//           Suc(BitSet(m')) <= {0} + Suc(BitSet(n'));
//         ==  { BitSet_Clauses(m'); BitSet_Clauses(n'); }
//           BitSet(2*m') <= BitSet(2*n' + 1);
//         }
//       case m == 2*m' + 1 && n == 2*n' =>
//         calc {
//           !EVEN(binom(n, m));
//         ==  { Lucas_Binary(n', m'); }
//           false;
//         ==  { assert 0 in BitSet(m) && 0 !in BitSet(n); }
//           BitSet(m) <= BitSet(n);
//         }
//       case m == 2*m' + 1 && n == 2*n' + 1 =>
//         calc {
//           !EVEN(binom(n, m));
//         ==  { Lucas_Binary(n', m'); }
//           !EVEN(binom(n', m'));
//         ==  { Lucas_Theorem(m', n'); }
//           BitSet(m') <= BitSet(n');
//         ==  { SucElements(BitSet(m')); SucElements(BitSet(n')); }
//           Suc(BitSet(m')) <= Suc(BitSet(n'));
//         ==  { ZeroNotInImageSuc(BitSet(m')); ZeroNotInImageSuc(BitSet(n')); }
//           ({0} + Suc(BitSet(m'))) <= {0} + Suc(BitSet(n'));
//         ==  { BitSet_Clauses(m'); BitSet_Clauses(n'); }
//           BitSet(2*m' + 1) <= BitSet(2*n' + 1);
//         }
//     }
//   }
// }