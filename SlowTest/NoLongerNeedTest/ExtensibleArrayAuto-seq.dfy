// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class {:autocontracts} ExtensibleArray<T> {
  ghost var Contents: seq<T>

  var elements: seq<T>
  var more: ExtensibleArray?<seq<T>>
  var length: int
  var M: int  // shorthand for:  if more == null then 0 else 256 * |more.Contents|

  predicate Valid()
  {
    // shape of data structure
    ((elements == [] && more == null && Contents == []) ||
     (elements != [] && |elements| == 256)) &&
    (more != null ==>
        // elements !in more.Repr &&
        |more.Contents| != 0 &&
        forall j :: 0 <= j < |more.Contents| ==>
            more.Contents[j] != [] && |more.Contents[j]| == 256 &&
            // more.Contents[j] in Repr && more.Contents[j] !in more.Repr &&
            more.Contents[j] != elements &&
            forall k :: 0 <= k < |more.Contents| && k != j ==> more.Contents[j] != more.Contents[k]) &&

    // length
    M == (if more == null then 0 else 256 * |more.Contents|) &&
    0 <= length <= M + 256 &&
    (more != null ==> M < length) &&

    // Contents
    length == |Contents| &&
    (forall i :: 0 <= i < M ==> Contents[i] == more.Contents[i / 256][i % 256]) &&
    (forall i :: M <= i < length ==> Contents[i] == elements[i - M])
  }

  constructor Init()
    ensures Contents == []
  {
    elements := [];
    more := null;
    length := 0;
    M := 0;

    Contents := [];
  }

  method Get(i: int) returns (t: T)
    requires 0 <= i < |Contents|
    ensures t == Contents[i]
    decreases Repr
  {
    if M <= i {
      t := elements[i - M];
    } else {
      var arr := more.Get(i / 256);
      t := arr[i % 256];
    }
  }

  method Set(i: int, t: T)
    requires 0 <= i < |Contents|
    ensures Contents == old(Contents)[i := t]
  {
    if M <= i {
      elements := elements[i - M := t];
    } else {
      var arr := more.Get(i / 256);
      arr := arr[i % 256 := t];
    }
    Contents := Contents[i := t];
  }

  method Append(t: T)
    ensures Contents == old(Contents) + [t]
    decreases |Contents|
  {
    if elements == [] {
      elements := seq(256, (_ => t));
    }
    if length == 0 || length % 256 != 0 {
      // there is room in "elements"
      elements := elements[length - M := t];
    } else {
      if more == null {
        more := new ExtensibleArray.Init();
        Repr := Repr + {more} + more.Repr;
      }
      // "elements" is full, so move it into "more" and allocate a new array
      more.Append(elements);
      Repr := Repr + more.Repr;
      M := M + 256;
      elements := seq(256, (_ => t));
      // Repr := Repr + {elements};
      elements := elements[0 := t];
    }
    length := length + 1;
    Contents := Contents + [t];
  }
}

// method Main() {
//   var a := new ExtensibleArray.Init();
//   var n := 0;
//   while n < 256*256+600
//     invariant a.Valid() && fresh(a.Repr)
//     invariant |a.Contents| == n
//   {
//     a.Append(n);
//     n := n + 1;
//   }
//   var k := a.Get(570); print k, "\n";
//   k := a.Get(0); print k, "\n";
//   k := a.Get(1000); print k, "\n";
//   a.Set(1000, 23);
//   k := a.Get(0); print k, "\n";
//   k := a.Get(1000); print k, "\n";
//   k := a.Get(66000); print k, "\n";
// }
