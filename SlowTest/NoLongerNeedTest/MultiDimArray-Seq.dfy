// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class A {
  // all of the following array types are allowed
  var a: seq<int>;
  var b: seq<bool>;
  var c: seq <A>;
  var d: seq <A>;  // this is a synonym for array<A>
//   var e: array2 <A>;
  var e: seq < seq<A> >;
//   var f: array3 <A?>;
  var f: seq < seq< seq<A?> > >;
//   var g: array300 <A>; // 300-Dimentional Array: SLOW!
//  var h: array3000 <array2<int>>; // too big!

  method M0()
    // modifies a
  {
    if (5 <= |a| && |a| <= |b|) {
      var x := b[2];
      var y := a[1];
      var z := a[2];
    //   a[2] := a[2] + 1;
      var a' := a[2 := a[2] + 1]; // updated seq
      var a'' := a'[2 := a'[2] + 1]; // updated seq
      var a''' := a''[2 := a''[2] + 1]; // updated seq
      assert x == b[2];
      assert y == a[1];
      assert z == a'[2] - 1;
    }
  }

  method M1()
    // modifies a;
  {
    if (5 <= |a| && |a| <= |d|) {
      var x := d[2];
      var y := a[1];
      var z := a[2];
    //   a[2] := a[2] + 1;
      var a' := a[2 := a[2] + 1]; // updated seq
      assert y == a[1];
      assert z == a'[2] - 1;
      assert x == d[2];  // error: a and d may be equal
    }
  }

//   method M2(i: int, j: int, k: int, val: A)
//     requires 0 <= i && i < |f0|;
//     requires 0 <= j && j < |f1|;
//     requires 0 <= k && k < |f2|;
//     // modifies f;
//   {
//     if (*) {
//       if (k < |f0|) {
//         var save := f[k,j,k];
//         f[i,j,k] := val;
//         assert save == f[k,j,k];  // error: k and i may be equal
//       }
//     } else if (k < f.Length0 && k != i) {
//       if (k < f.Length0) {
//         var save := f[k,j,k];
//         f[i,j,k] := val;
//         assert save == f[k,j,k];  // fine
//       }
//     }
//   }

//   method M3(i: int, j: int, k: int)
//     requires 0 <= i && i < f.Length0;
//     requires 0 <= j && j < f.Length1;
//     requires 0 <= k && k < f.Length2;
//     modifies f;
//     decreases i;
//   {
//     if (i != 0) {
//       var z := new A?[2,3,5];  // first three primes (nice!)
//       var s := z[1,2,4];  // first three powers of 2 (tra-la-la)
//       var some: A?;
//       f[i,j,k] := some;
//       M3(i-1, j, k);
//       assert s == z[1,2,4];
//       if (*) {
//         assert f[i,j,k] == some;  // error: the recursive call may have modified any element in 'f'
//       }
//     }
//   }

//   method M4(a: array2<bool>) returns (k: int)
//     ensures 0 <= k;
//   {
//     k := a.Length0 + a.Length1;
//   }
}
