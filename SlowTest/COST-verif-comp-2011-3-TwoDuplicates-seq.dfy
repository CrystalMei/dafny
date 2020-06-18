// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
predicate IsDuplicate(a: seq<int>, p: int)
//   reads a
{
  IsPrefixDuplicate(a, |a|, p)
}

predicate IsPrefixDuplicate(a: seq<int>, k: int, p: int)
  requires 0 <= k <= |a|;
//   reads a;
{
  exists i,j :: 0 <= i < j < k && a[i] == a[j] == p
}

method Search(a: seq<int>) returns (p: int, q: int, d: seq<int>)
  requires 4 <= |a|;
  requires exists p,q :: p != q && IsDuplicate(a, p) && IsDuplicate(a, q);  // two distinct duplicates exist
  requires forall i :: 0 <= i < |a| ==> 0 <= a[i] < |a| - 2;  // the elements of "a" in the range [0.. a.Length-2]
  ensures p != q && IsDuplicate(a, p) && IsDuplicate(a, q);
{
  // allocate an array "d" and initialize its elements to -1.
  d := seq(|a| - 2, _ => -1);
  var i := 0;
  assert |d| == |a| - 2;
  while (i < |d|)
    invariant 0 <= i <= |d| && forall j :: 0 <= j < i ==> d[j] == -1;
    invariant |d| == |a| - 2;
  {
    d := d[i := -1];
    i := i + 1;
  }
  assert |d| == |a| - 2;

  i, p, q := 0, 0, 1;
  while (true)
    invariant 0 <= i < |a|;
    invariant |d| == |a| - 2;
    invariant forall j :: 0 <= j < |d| ==>
                (d[j] == -1 && forall k :: 0 <= k < i ==> a[k] != j) ||
                (0 <= d[j] < i && a[d[j]] == j);
    invariant p == q ==> IsDuplicate(a, p); //WISH remove the trigger on the next line
    invariant forall k {:trigger old(a[k])} :: 0 <= k < i && IsPrefixDuplicate(a, i, a[k]) ==> p == q == a[k];
    decreases |a| - i;
  {
    var k := d[a[i]];
    assert k < i;  // note, this assertion is really for human consumption; it is not needed by the verifier, and it does not change the performance of the verifier
    if (k == -1) {
      // a[i] does not exist in a[..i]
      d := d[a[i] := i];
      assert |d| == |a| - 2;
    } else {
      // we have encountered a duplicate
      assert a[i] == a[k] && IsDuplicate(a, a[i]);  // note, this assertion is really for human consumption; it is not needed by the verifier, and it does not change the performance of the verifier
      if (p != q) {
        // this is the first duplicate encountered
        p, q := a[i], a[i];
      } else if (p == a[i]) {
        // this is another copy of the same duplicate we have seen before
      } else {
        // this is the second duplicate
        q := a[i];
        return;
      }
    }
    i := i + 1;
  }
}
