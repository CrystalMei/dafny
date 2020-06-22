// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


datatype Option<T> = None | Some(v:T) 
datatype Composite = Composite(left: Option<Composite>, right: Option<Composite>, parent: Option<Composite>, val: int, sum: int)

predicate Valid (c: Composite, S: set<Composite>)
{
    c in S &&
    (c.parent != None ==> c.parent.v in S && ((c.parent.v.left.Some? && c.parent.v.left.v == c) || (c.parent.v.right.Some? && c.parent.v.right.v == c))) &&
    (c.left != None ==> c.left.v in S && c.left.v.parent.Some? && c.left.v.parent.v == c && c.left != c.right) &&
    (c.right != None ==> c.right.v in S && c.right.v.parent.Some? && c.right.v.parent.v == c && c.left != c.right) &&
    c.sum == c.val + (if c.left == None then 0 else c.left.v.sum) + (if c.right == None then 0 else c.right.v.sum)
}

predicate Acyclic (c: Composite, S: set<Composite>)
    decreases c, S
{
    c in S &&
    (c.parent != None ==> Acyclic(c.parent.v, S - {c}))
}

method Init(x: int) returns (c: Composite)
    ensures Valid(c, {c}) && Acyclic(c, {c}) && c.val == x && c.parent == None
{
    c := Composite(None, None, None, x, x);
}

method Update(c: Composite, x: int, S: set<Composite>) returns (c': Composite, S': set<Composite>)
    requires c in S && Acyclic(c, S)
    requires forall x :: x in S ==> Valid(x, S)
    // modifies S
    ensures c' in S'
    ensures forall x :: x in S' ==> Valid(x, S')
    ensures forall x :: x in S ==> x != c' ==> x in S'
    ensures c'.val == x
{
    var delta := x - c.val;
    c' := Composite(c.left, c.right, c.parent, x, c.sum);
    S' := Adjust(c', delta, S, S);
}

method Add(c: Composite, S: set<Composite>, child: Composite, U: set<Composite>) returns (c': Composite, S': set<Composite>, child': Composite)
    requires c in S && Acyclic(c, S)
    requires forall x :: x in S ==> Valid(x, S)
    requires child in U
    requires forall x :: x in U ==> Valid(x, U)
    requires S !! U
    requires c.left == None || c.right == None
    requires child.parent == None
    // modifies only one of this.left and this.right, and child.parent, and various sum fields:
    // modifies S, child
    ensures child'.left == child.left && child'.right == child.right && child'.val == child.val
    ensures forall x :: x in S' && x != c' ==> x in S
    ensures forall x :: x in S' ==> c.parent == old(c.parent) && c.val == old(c.val)
    ensures c.left != None ==> c'.left == c.left
    ensures c.right != None ==> c'.right == c.right
    // sets child.parent to this:
    ensures child'.parent.Some? && child'.parent.v == c
    // leaves everything in S+U valid
    ensures forall x: Composite {:autotriggers false} :: x in S'+U ==> Valid(x, S'+U) // We can't generate a trigger for this at the moment; if we did, we would still need to prevent TrSplitExpr from translating c in S+U to S[c] || U[c].
{
    if (c.left == None) {
        c' := Composite(Some (child), c.right, c.parent, c.val, c.sum);
    } else {
        c' := Composite(c.left, Some(child), c.parent, c.val, c.sum);
    }
    child' := Composite(child.left, child.right, Some(c'), child.val, child.sum);
    Adjust(c', child'.sum, S, S+U);
}

method Dislodge(c: Composite, ghost S: set<Composite>) returns (c': Composite)
    requires c in S && Acyclic(c, S)
    requires forall x :: x in S ==> Valid(x, S)
    // modifies S
    ensures forall x :: x in S ==> Valid(x, S)
    ensures c'.parent == None
    ensures forall x :: x in S ==> x.val == old(x.val)
    ensures forall x :: x in S && x != c' ==> c.parent == old(c.parent)
    ensures forall x :: x in S ==> x.left == old(x.left) || (old(x.left.v) == c && x.left == None)
    ensures forall x :: x in S ==> x.right == old(x.right) || (old(x.right.v) == c && x.right == None)
    ensures Acyclic(c', {c'})
{
    var p := c.parent;
    c' := Composite(c.left, c.right, None, c.val, c.sum);
    if (p != None) {
        if (p.v.left.v == c') {
            p := Some (Composite(None, p.v.right, p.v.parent, p.v.val, p.v.sum));
        } else {
            p := Some (Composite(p.v.left, None, p.v.parent, p.v.val, p.v.sum));
        }
        var delta := -c'.sum;
        Adjust(p.v, delta, S - {c'}, S);
    }
}

method Adjust(c: Composite, delta: int, ghost U: set<Composite>, ghost S: set<Composite>)
    requires U <= S && Acyclic(c, U)
    // everything else is valid:
    requires forall x :: x in S && x != c ==> Valid(x, S)
    // this is almost valid:
    requires c.parent != None ==> c.parent.v in S && ((c.parent.v.left.Some? && c.parent.v.left.v == c) || (c.parent.v.right.Some? && c.parent.v.right.v == c))
    requires c.left != None ==> c.left.v in S && c.left.v.parent.Some? && c.left.v.parent.v == c && c.left != c.right
    requires c.right != None ==> c.right.v in S && c.right.v.parent.Some? && c.right.v.parent.v == c && c.left != c.right
    // ... except that sum needs to be adjusted by delta:
    requires c.sum + delta == c.val + (if c.left == None then 0 else c.left.v.sum) + (if c.right == None then 0 else c.right.v.sum)
    // modifies sum fields in U:
    // modifies U`sum
    // everything is valid, including this:
    ensures forall x :: x in S ==> Valid(x, S)
  {
    // var p: Composite? := this;
    // ghost var T := U;
    // while (p != null)
    //   invariant T <= U
    //   invariant p == null || p.Acyclic(T)
    //   invariant forall c :: c in S && c != p ==> c.Valid(S)
    //   invariant p != null ==> p.sum + delta == p.val + (if p.left == null then 0 else p.left.sum) + (if p.right == null then 0 else p.right.sum)
    //   invariant forall c :: c in S ==> c.left == old(c.left) && c.right == old(c.right) && c.parent == old(c.parent) && c.val == old(c.val)
    //   decreases T
    // {
    //   p.sum := p.sum + delta;
    //   T := T - {p};
    //   p := p.parent;
    // }
  }