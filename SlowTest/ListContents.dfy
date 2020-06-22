// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node<T> {
  ghost var List: seq<T>
  ghost var Repr: set<Node<T>>

  var data: T
  var next: Node?<T>

  predicate Valid()
    reads this, Repr
  {
    this in Repr &&
    (next == null ==> List == [data]) &&
    (next != null ==>
        next in Repr && next.Repr <= Repr &&
        this !in next.Repr &&
        List == [data] + next.List &&
        next.Valid())
  }

  constructor (d: T)
    ensures Valid() && fresh(Repr - {this})
    ensures List == [d]
  {
    data, next := d, null;
    List, Repr := [d], {this};
  }

  constructor InitAsPredecessor(d: T, succ: Node<T>)
    requires succ.Valid()
    ensures Valid() && fresh(Repr - {this} - succ.Repr)
    ensures List == [d] + succ.List
  {
    data, next := d, succ;
    List := [d] + succ.List;
    Repr := {this} + succ.Repr;
  }

  method ReverseInPlace() returns (reverse: Node<T>)
    requires Valid()
    modifies Repr
    ensures reverse.Valid() && reverse.Repr <= old(Repr)
    ensures |reverse.List| == |old(List)|
    ensures forall i :: 0 <= i < |reverse.List| ==> reverse.List[i] == old(List)[|old(List)|-1-i]
  {
    var current := next;
    reverse := this;
    reverse.next := null;
    reverse.Repr := {reverse};
    reverse.List := [data];

    while current != null
      invariant reverse.Valid() && reverse.Repr <= old(Repr)
      invariant current == null ==> |old(List)| == |reverse.List|
      invariant current != null ==>
        current.Valid() &&
        current in old(Repr) && current.Repr <= old(Repr) &&
        current.Repr !! reverse.Repr
      invariant current != null ==>
        |old(List)| == |reverse.List| + |current.List| &&
        current.List == old(List)[|reverse.List|..]
      invariant forall i :: 0 <= i < |reverse.List| ==> reverse.List[i] == old(List)[|reverse.List|-1-i]
      decreases if current != null then |current.List| else -1
    {
      var nx := current.next;

      // ..., reverse, current, nx, ...
      current.next := reverse;
      current.Repr := {current} + reverse.Repr;
      current.List := [current.data] + reverse.List;

      reverse := current;
      current := nx;
    }
  }
}