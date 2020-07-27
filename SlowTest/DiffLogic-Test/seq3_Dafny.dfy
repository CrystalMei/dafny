function method SeqUpdate<X> (s: seq<X>, k: int, v: X) : (s': seq<X>)
    requires 0 <= k < |s|
    ensures |s| == |s'|
    ensures forall i :: 0 <= i < |s| ==>
        if i < k then s'[i] == s[i]
        else if i == k then s'[k] == v
        else s'[i] == s[i]

method Sequence(s: seq<bool>, j: int, b: bool, c: bool) returns (t: seq<bool>)
    requires 10 <= |s|
    requires 8 <= j < |s|
    ensures |t| == |s|
    ensures t[8] == s[8] || t[9] == s[9]
    ensures t[j] == b
  {
    if (c) {
      t := s[j := b];
    } else {
        t := SeqUpdate<bool> (s, j, b);
    //   t := s[..j] + [b] + s[j+1..];
    }
  }
