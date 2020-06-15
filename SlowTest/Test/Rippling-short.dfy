// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Datatypes

datatype Nat = Zero | Suc(Nat)

datatype List = Nil | Cons(Nat, List)

// List functions
function concat(xs: List, ys: List): List
{
  match xs
  case Nil => ys
  case Cons(x,tail) => Cons(x, concat(tail, ys))
}

function reverse(xs: List): List
{
  match xs
  case Nil => Nil
  case Cons(t, rest) => concat(reverse(rest), Cons(t, Nil))
}

lemma Lemma_RevConcat(xs: List, ys: List)
  ensures reverse(concat(xs, ys)) == concat(reverse(ys), reverse(xs));
{
  match (xs) {
    case Nil =>
      assert forall ws :: concat(ws, Nil) == ws;
    case Cons(t, rest) =>
      assert forall a, b, c :: concat(a, concat(b, c)) == concat(concat(a, b), c);
  }
}