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
      t := s[..j] + [b] + s[j+1..];
    }
  }
