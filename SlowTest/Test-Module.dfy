module A {
  export Basic
    provides AbInt, AbSeq, I2A, AbLt, AbSub, AbLeq, AbSeqLen, AbSeqIn, AbSeqIndex, AbSeqSlice
    reveals I0

  type AbInt(!new)(==) = int

  type AbSeq<X(==)> = seq<X>

  const I0 : AbInt := I2A(0)
  function method I2A (n: int) : (AbInt) { n }

  function method AbLt (n: AbInt, m: AbInt) : bool { n < m }
  function method AbSub (n: AbInt, m: AbInt) : AbInt { n - m }
  function method AbLeq (n: AbInt, m: AbInt) : (r: bool)
    ensures AbLeq(n, m) <==> AbLt(n, m) || n == m
    { n <= m }
  function method AbSeqLen<X> (s: AbSeq<X>) : AbInt { |s| }
  function method AbSeqIn<X> (v: X, s: AbSeq<X>) : bool { v in s }
  function method AbSeqIndex<X> (i: AbInt, s: AbSeq<X>) : X
    requires AbLeq(I0, i)
    requires AbLt(i, AbSeqLen(s))
    ensures AbSeqIn(AbSeqIndex(i, s), s)
    { s[i] }

  function method AbSeqSlice<X> (i: AbInt, j: AbInt, s: AbSeq<X>) : (s' : AbSeq<X>)
    requires AbLeq(I0, i)
    requires AbLeq(j, AbSeqLen(s))
    requires AbLeq(i, j)
    ensures AbSeqLen(s') == AbSub(j, i)
    ensures forall x :: AbLeq(i, x) && AbLt(x, j) ==>
      // precond begins
      AbLeq(I0, x) ==> AbLt(x, AbSeqLen(s)) ==>
      AbLeq(I0, AbSub(x, i)) ==> AbLt(AbSub(x, i), AbSeqLen(s')) ==>
      // precond ends
      AbSeqIndex(x, s) == AbSeqIndex(AbSub(x, i), s') // s[i..j] w/ s[i] and w/o s[j]
    { s[i..j] }
}