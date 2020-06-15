// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<T> = Nil | Cons(hd: T, tl: List)

// ---------------------------------------------------

// The followinng functions and methods are oblivious of the fact that
// List takes a type parameter.

function concat(xs: List, ys: List): List
{
  match xs
  case Nil => ys
  case Cons(x, tail) => Cons(x, concat(tail, ys))
}

function reverse(xs: List): List
{
  match xs
  case Nil => Nil
  case Cons(t, rest) => concat(reverse(rest), Cons(t, Nil))
}

ghost method Lemma<A>(xs: List, ys: List)
  ensures reverse(concat(xs, ys)) == concat(reverse(ys), reverse(xs));
{
  match (xs) {
    case Nil =>
      assert forall ws :: concat(ws, Nil) == var ws : List<A> := ws; ws;
    case Cons(t, rest) =>
      assert forall a, b, c :: concat(a, concat(b, c)) == var ws : List <A> := concat(concat(a, b), c); ws;
  }
}

// ------ Here are some test cases where the inferred arguments will be a prefix of the given ones

// method DoAPrefix<A, B, C>(xs: List) returns (ys: List<A>)
// {
//   ys := xs;
// }

function FDoAPrefix<A, B, C>(xs: List): List<A>
{
  xs
}
