// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Option<T> = Some(o: T) | None
datatype Eseq<T> = Eseq(Contents: seq<T>, elements: Option< seq<T> >, more: Option< Eseq <seq<T> > >, length: int, M: int)

predicate Valid(s: Eseq)
{
  ( (s.elements == None && s.more == None && s.Contents == []) ||
    (s.elements != None && |s.elements.o| == 256)
  ) &&

  ( s.more != None ==>
    Valid (s.more.o) &&
    |s.more.o.Contents| != 0 &&
    forall j :: 0 <= j < |s.more.o.Contents| ==>
      s.more.o.Contents[j] != [] && |s.more.o.Contents[j]| == 256 &&
      s.more.o.Contents[j] != s.elements.o &&
      forall k :: 0 <= k < |s.more.o.Contents| && k != j ==>
        s.more.o.Contents[j] != s.more.o.Contents[k]
  ) &&

  // length
  s.M == (if s.more == None then 0 else 256 * |s.more.o.Contents|) &&
  0 <= s.length <= s.M + 256 &&
  (s.more != None ==> s.M < s.length) &&

  // Contents
  s.length == |s.Contents| &&
  (forall i :: 0 <= i < s.M ==> s.Contents[i] == s.more.o.Contents[i / 256][i % 256]) &&
  (forall i :: s.M <= i < s.length ==> s.Contents[i] == s.elements.o[i - s.M])  
}

function Init<T>(): (s:Eseq<T>)
  ensures Valid(s)
  ensures s.Contents == []
{
  Eseq([], None, None, 0, 0)
}

method Get<T>(s: Eseq<T>, i: int) returns (t: T)
  requires Valid(s)
  requires 0 <= i < |s.Contents|
  ensures t == s.Contents[i]
  {
    if s.M <= i {
      t := s.elements.o[i - s.M];
    } else {
      var arr := Get(s.more.o, i / 256);
      t := arr[i % 256];
    }
  }

method Set<T>(s: Eseq<T>, i: int, t: T) returns (s': Eseq<T>)
  requires Valid(s)
  requires 0 <= i < |s.Contents|
  ensures s'.Contents == old(s.Contents)[i := t]
{
  s' := s; // duplicate s for modification
  var Eseq(Contents, elements, more, length, M) := s';
  if M <= i {
    s' := Eseq(s'.Contents, Some (s'.elements.o[i - M := t]), s'.more, s'.length, s'.M);
  } else {
    var arr := Get(more.o, i / 256);
    arr := arr[i % 256 := t];
  }
  s' := Eseq(Contents[i := t], elements, more, length, M);
}

method Append<T>(s: Eseq<T>, t: T) returns (s': Eseq<T>)
  requires Valid(s)
  ensures s'.Contents == s.Contents + [t]
  // decreases |s.Contents|
{
  s' := s;
  var Eseq(Contents, elements, more, length, M) := s';
  if s'.elements == None {
    s' := Eseq(s'.Contents, Some (seq(256, (_ => t))), s'.more, s'.length, s'.M);
  }
  if s'.length == 0 || s'.length % 256 != 0 {
    // there is room in "elements"
    s' := Eseq(s'.Contents, Some (s'.elements.o[s'.length - M := t]), s'.more, s'.length, s'.M);
  } else {
    if s.more == None {
      s':= Eseq(s'.Contents, s'.elements, Some(Init()), s'.length, s'.M);
    }
    // "elements" is full, so move it into "more" and allocate a new array
    s' := Append(s'.more.o, s'.elements.o); // problem
    s' := Eseq(s'.Contents, Some (seq(256, (_ => t))), s'.more, s'.length, s'.M + 256);
    s' := Eseq(s'.Contents, Some (s'.elements.o[0 := t]), s'.more, s'.length, s'.M);
  }
  s' := Eseq(s'.Contents+ [t], s'.elements, s'.more, s'.length+1, s'.M);
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