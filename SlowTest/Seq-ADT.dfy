type AbInt(==)
function method int2adt (n: int) : (AbInt)
predicate AbIsZero (n: AbInt) { n == int2adt(0) }
predicate AbPos (n: AbInt) { !AbIsZero(n) }
// predicate AbNonNeg (n: AbInt) { true }
function method AbLt(n: AbInt, m: AbInt) : bool
function method AbAdd(n: AbInt, m: AbInt) : (r: AbInt)

datatype AbSeq<X> = N | C(hd: (X), tl: AbSeq<X>)
function method AbSeqIndex (s: AbSeq<AbInt>, i: AbInt) : AbInt
function method AbSeqLen (s: AbSeq<AbInt>) : AbInt
function method AbSeqAppend (s1: AbSeq<AbInt>, s2: AbSeq<AbInt>) : AbSeq<AbInt>
function method AbSeqIn (v: AbInt, s: AbSeq<AbInt>) : bool
  decreases s
{
  match s
  case N => false
  case C(hd, tl) => if hd == v then true else AbSeqIn(v, tl)
}

lemma Seq_Props ()
  ensures forall s: AbSeq<AbInt> :: AbSeqLen(s) == int2adt(0) || AbLt(int2adt(0), AbSeqLen(s)) // |s| >= 0
  ensures forall s: AbSeq<AbInt> :: s.N? ==> AbSeqLen(s) == int2adt(0) // empty s ==> |s| == 0
  ensures forall s: AbSeq<AbInt> :: AbSeqLen(s) == int2adt(0) ==> s.N? // |s| == 0 ==> empty s
  ensures forall s: AbSeq<AbInt> :: AbLt(int2adt(0), AbSeqLen(s)) ==> s.C? // |s| > 0 ==> non-empty s

  ensures forall x: AbInt :: AbSeqLen(C(x, N)) == int2adt(1) // |[x]| == 1

  ensures forall x: AbInt, s: AbSeq<AbInt> :: AbSeqLen(C(x, s)) == AbAdd(AbSeqLen(s), int2adt(1)) // |[x] + s| == |s| + 1 

  ensures forall s1: AbSeq<AbInt>, s2: AbSeq<AbInt> :: AbSeqLen(AbSeqAppend(s1, s2)) == AbAdd(AbSeqLen(s1), AbSeqLen(s2)) // |s1 + s2| == |s1| + |s2|

  ensures forall x: AbInt, s1: AbSeq<AbInt>, s2: AbSeq<AbInt> :: AbSeqIn(x, s1) && AbSeqIn(x, s2) ==> AbSeqIn(x, AbSeqAppend(s1, s2))
