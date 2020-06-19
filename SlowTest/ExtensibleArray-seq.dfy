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
    s' := Append(s'.more.o, s'.elements.o);
    s' := Eseq(s'.Contents, Some (seq(256, (_ => t))), s'.more, s'.length, s'.M + 256);
    s' := Eseq(s'.Contents, Some (s'.elements.o[0 := t]), s'.more, s'.length, s'.M);
  }
  s' := Eseq(s'.Contents+ [t], s'.elements, s'.more, s'.length+1, s'.M);
}

// class ExtensibleArray<T> {
//   ghost var Contents: seq<T>
//   ghost var Repr: set<object?>
//   var elements: seq<T>
//   var more: ExtensibleArray?<seq<T>>
//   var length: int
//   var M: int  // shorthand for:  if more == null then 0 else 256 * |more.Contents|

//   predicate Valid()
//     reads this, Repr
//   {
//     // shape of data structure
//     this in Repr && null !in Repr &&
//     ((elements == [] && more == null && Contents == []) ||
//      (elements != [] && |elements| == 256 /*&& elements in Repr*/)) &&
//     (more != null ==>
//         more in Repr && more.Repr <= Repr && this !in more.Repr && /*elements !in more.Repr && */
//         more.Valid() &&
//         |more.Contents| != 0 &&
//         forall j :: 0 <= j < |more.Contents| ==>
//             more.Contents[j] != [] && |more.Contents[j]| == 256 &&
//             /* more.Contents[j] in Repr && more.Contents[j] !in more.Repr && */
//             more.Contents[j] != elements &&
//             forall k :: 0 <= k < |more.Contents| && k != j ==> more.Contents[j] != more.Contents[k]) &&

//     // length
//     M == (if more == null then 0 else 256 * |more.Contents|) &&
//     0 <= length <= M + 256 &&
//     (more != null ==> M < length) &&

//     // Contents
//     length == |Contents| &&
//     (forall i :: 0 <= i < M ==> Contents[i] == more.Contents[i / 256][i % 256]) &&
//     (forall i :: M <= i < length ==> Contents[i] == elements[i - M])
//   }

//   constructor Init()
//     ensures Valid() && fresh(Repr - {this})
//     ensures Contents == []
//   {
//     elements := [];
//     more := null;
//     length := 0;
//     M := 0;

//     Contents := [];
//     Repr := {this};
//   }

//   method Get(i: int) returns (t: T)
//     requires Valid()
//     requires 0 <= i < |Contents|
//     ensures t == Contents[i]
//     decreases Repr
//   {
//     if M <= i {
//       t := elements[i - M];
//     } else {
//       var arr := more.Get(i / 256);
//       t := arr[i % 256];
//     }
//   }

//   method Set(i: int, t: T)
//     requires Valid()
//     requires 0 <= i < |Contents|
//     modifies Repr
//     ensures Valid() && fresh(Repr - old(Repr))
//     ensures Contents == old(Contents)[i := t]
//   {
//     if M <= i {
//       elements := elements[i-M := t];
//     } else {
//       var arr := more.Get(i / 256);
//       arr := arr[i % 256 := t];
//     }
//     Contents := Contents[i := t];
//   }

// // ~ 4s
//   method Append(t: T)
//     requires Valid()
//     modifies Repr
//     ensures Valid() && fresh(Repr - old(Repr))
//     ensures Contents == old(Contents) + [t]
//     decreases |Contents|
//   {
//     if elements == [] {
//       elements := seq(256, (_ => t));
//       // Repr := Repr + {elements};
//     }
//     if length == 0 || length % 256 != 0 {
//       // there is room in "elements"
//       elements := elements[length - M := t];
//     } else {
//       if more == null {
//         more := new ExtensibleArray.Init();
//         Repr := Repr + {more} + more.Repr;
//       }
//       // "elements" is full, so move it into "more" and allocate a new array
//       more.Append(elements);
//       Repr := Repr + more.Repr;
//       M := M + 256;
//       elements := seq(256, (_ => t));
//       // Repr := Repr + {elements};
//       elements:= elements[0 := t];
//     }
//     length := length + 1;
//     Contents := Contents + [t];
//   }
// }

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