type AbInt(==)
function method int2adt (n: int) : (AbInt)
predicate AbIsZero (n: AbInt) { n == int2adt(0) }
predicate AbPos (n: AbInt) { !AbIsZero(n) }
// predicate AbNonNeg (n: AbInt) { true }
function method AbLt(n: AbInt, m: AbInt) : bool
function method AbInc1(n: AbInt) : AbInt
function method AbInc(n: AbInt, m: AbInt) : AbInt
function method AbDec1(n: AbInt) : AbInt

lemma Props_inc_one ()
  ensures forall x :: AbInc1(x) == AbInc(x, int2adt(1)) == AbInc(int2adt(1), x)
lemma Props_inc_zero ()
  ensures forall x :: AbInc(x, int2adt(0)) == AbInc(int2adt(0), x) == x
lemma Props_inc_associative () // (x + y) + z == x + (y + z)
  ensures forall x, y, z :: AbInc(AbInc(x, y), z) == AbInc(x, AbInc(y, z))

datatype AbSeq<X> = N | C(hd: X, tl: AbSeq<X>)
function method AbSeqIndex (s: AbSeq<(AbInt, AbInt)>, i: AbInt) : AbInt
function method AbSeqLen (s: AbSeq<(AbInt, AbInt)>) : AbInt
function method AbSeqConcat<X> (s1: AbSeq<X>, s2: AbSeq<X>) : AbSeq<X>
function method AbSeqIn (v: AbInt, s: AbSeq<(AbInt, AbInt)>) : bool
//   decreases s
// {
//   match s
//   case N => false
//   case C(hd, tl) => if hd.1 == v then true else AbSeqIn(v, tl)
// }

// lemma Seq_Props ()
  // ensures forall s: AbSeq<AbInt> :: AbSeqLen(s) == int2adt(0) || AbLt(int2adt(0), AbSeqLen(s)) // |s| >= 0
lemma Seq_Props_length_empty ()
  ensures forall s: AbSeq :: s.N? <==> AbSeqLen(s) == int2adt(0) // empty s <==> |s| == 0
lemma Seq_Props_length_singleton ()
  ensures forall x, y :: AbSeqLen(C((x, y), N)) == int2adt(1) // |[x]| == 1
lemma Seq_Props_length_one_more () // |C(hd, tl)| == 1 + |tl|
  ensures forall x: AbInt, y: AbInt, tl: AbSeq :: AbSeqLen(C((x, y), tl)) == AbInc1(AbSeqLen(tl))
//   ensures forall s: AbSeq<AbInt> :: AbLt(int2adt(0), AbSeqLen(s)) ==> s.C? // |s| > 0 ==> non-empty s
lemma Seq_Props_concat_length () // |s1 + s2| == |s1| + |s2|
  ensures forall s1: AbSeq, s2: AbSeq :: AbSeqLen(AbSeqConcat(s1, s2)) == AbInc(AbSeqLen(s1), AbSeqLen(s2))
lemma Seq_Props_concat_in () // x in s1 || x in s2 <==> x in s1 + s2
  ensures forall x: AbInt, s1: AbSeq, s2: AbSeq :: AbSeqIn(x, s1) || AbSeqIn(x, s2) <==> AbSeqIn(x, AbSeqConcat(s1, s2))
  ensures forall x: AbInt, s1: AbSeq, s2: AbSeq :: !AbSeqIn(x, s1) && !AbSeqIn(x, s2) <==> !AbSeqIn(x, AbSeqConcat(s1, s2))
lemma Seq_Props_concat_in_sub () // x in s1 ==> x in s1 + s2
  ensures forall x: AbInt, s1: AbSeq, s2: AbSeq :: AbSeqIn(x, s1) ==> AbSeqIn(x, AbSeqConcat(s1, s2))
  ensures forall x: AbInt, s1: AbSeq, s2: AbSeq :: AbSeqIn(x, s2) ==> AbSeqIn(x, AbSeqConcat(s1, s2))
lemma Seq_Props_in_seq () // x in [hd, tl] <==> x in hd || x in tl
  ensures forall a: AbInt, x: AbInt, y: AbInt, tl: AbSeq :: AbSeqIn(a, C((x, y), tl)) <==> AbSeqIn(a, tl) || a == y
  ensures forall a: AbInt, x: AbInt, y: AbInt, tl: AbSeq :: !AbSeqIn(a, C((x, y), tl)) <==> !AbSeqIn(a, tl) && a != y
lemma Seq_Props_in_head () // x in [x,tl]
  ensures forall a: AbInt, x: AbInt, y: AbInt, tl: AbSeq :: a == y ==> AbSeqIn(a, C((x, y), tl))
lemma Seq_Props_in_tail () // x in tl ==> x in [hd,tl]
  ensures forall a: AbInt, x: AbInt, y: AbInt, tl: AbSeq :: AbSeqIn(a, tl) ==> AbSeqIn(a, C((x, y), tl))
  ensures forall a: AbInt, x: AbInt, y: AbInt, tl: AbSeq :: AbSeqIn(a, C((x, y), tl)) && a != y ==> AbSeqIn(a, tl)
lemma Seq_Props_in_singleton () // x in [x] && x !in [y]
  ensures forall a, x, y :: AbSeqIn(a, C((x, y), N)) <==> a == y
  ensures forall a, x, y :: !AbSeqIn(a, C((x, y), N)) <==> a != y
lemma Seq_Props_in_empty ()
  ensures forall x: AbInt :: !AbSeqIn(x, N)
lemma Seq_Props_in_non_empty ()
  ensures forall x: AbInt, s: AbSeq :: AbSeqIn(x, s) ==> s != N

function method AbSeqRemove (i: AbInt, s: AbSeq<(AbInt, AbInt)>): (s': AbSeq<(AbInt, AbInt)>)
  requires AbSeqIn(i, s)
  ensures !AbSeqIn(i, s')
  ensures AbSeqLen(s) == AbInc1(AbSeqLen(s'))
{
  var r := AbSeqRemoveHelper(i, N, s);
  assert r.1 == N;
  r.0
}

function method AbSeqRemoveHelper (i: AbInt, head: AbSeq<(AbInt, AbInt)>, tail: AbSeq<(AbInt, AbInt)>): (r: (AbSeq<(AbInt, AbInt)>, AbSeq<(AbInt, AbInt)>))
  requires AbSeqIn(i, tail)
  ensures forall x :: AbSeqIn(x, head) ==> AbSeqIn(x, r.0)
  ensures forall x :: AbSeqIn(x, tail) && x != i ==> AbSeqIn(x, r.0)
  ensures AbInc(AbSeqLen(head), AbSeqLen(tail)) == AbInc1(AbInc(AbSeqLen(r.0), AbSeqLen(r.1))) // length
  decreases tail
{
  match tail
  case N => Seq_Props_in_empty (); (head, N)
  case C(hd, tl) =>
    if hd.1 == i then
      Seq_Props_in_tail ();
      Seq_Props_length_one_more ();
      Props_inc_one ();
      Props_inc_associative ();
      AbSeqDecTail(head, tl)
    else
      Seq_Props_in_tail ();
      Seq_Props_length_one_more ();
      Seq_Props_concat_in_sub ();
      Seq_Props_concat_length ();
      Props_inc_one ();
      Props_inc_associative ();
      var res := AbSeqRemoveHelper(i, AbSeqConcat(head, C(hd, N)), tl);
      assert forall x :: AbSeqIn(x, head) ==> AbSeqIn(x, res.0);
      assert forall x :: AbSeqIn(x, tail) && x != i ==> AbSeqIn(x, res.0);
      assert AbInc(AbSeqLen(head), AbSeqLen(tail)) == AbInc1(AbInc(AbSeqLen(res.0), AbSeqLen(res.1)));
      res
}

// all elements in tail: index - 1, and concat with head
// return (head', N)
function method AbSeqDecTail (head: AbSeq<(AbInt, AbInt)>, tail: AbSeq<(AbInt, AbInt)>): (r: (AbSeq<(AbInt, AbInt)>, AbSeq<(AbInt, AbInt)>))
  ensures tail == N ==> AbSeqLen(r.0) == AbSeqLen(head)
  ensures AbInc(AbSeqLen(head), AbSeqLen(tail)) == AbInc(AbSeqLen(r.0), AbSeqLen(r.1)) // length
  ensures forall x :: AbSeqIn(x, tail) ==> AbSeqIn(x, r.0) // content
  ensures forall x :: AbSeqIn(x, head) ==> AbSeqIn(x, r.0) // content
  ensures forall x :: !AbSeqIn(x, head) && !AbSeqIn(x, tail) ==> !AbSeqIn(x, r.0) // content
  // ensures about index?
  decreases tail
{
  match tail
  case N =>
    Seq_Props_in_empty ();
    (head, N)
  case C(hd, tl) =>
    var hd' := (AbDec1(hd.0), hd.1); // index - 1
    // length ensure
    Seq_Props_length_singleton ();
    Seq_Props_concat_length ();
    Props_inc_one ();
    Props_inc_associative ();
    Seq_Props_length_one_more ();
    // content ensure
    Seq_Props_concat_in ();
    Seq_Props_in_seq ();
    Seq_Props_in_head ();
    Seq_Props_in_singleton ();
    AbSeqDecTail(AbSeqConcat(head, C(hd', N)), tl)
}
