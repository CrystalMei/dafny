// dafny/Test/dafny4/git-issue96.dfy


lemma addition_bound_instance ()
    ensures forall i, j {:trigger i + j} :: 0 <= i && 0 <= j ==> 0 <= i + j
    ensures forall i, j {:trigger i + j} :: i < 5 && j < 5 ==> i + j < 10

lemma addition_bound (l: int, h: int)
    ensures forall i, j {:trigger i + j} :: l <= i && l <= j ==> l + l <= i + j
    ensures forall i, j {:trigger i + j} :: i < h && j < h ==> i + j < h + h

predicate P(s:seq<int>)
    requires 10 < |s|
{
    addition_bound_instance ();
    assume (forall i, j {:trigger i + j} :: i + j < 10 ==> i + j < |s|);
    (forall i:int {:trigger s[i]} :: forall j:int {:trigger s[j]} ::
        0 <= i < j < 5 ==> s[i + j] == s[i] == s[j])
}

predicate P0(s:seq<int>)
    requires 10 < |s|
{
    addition_bound_instance ();
    assume (forall i, j {:trigger i + j} :: i + j < 10 ==> i + j < |s|);
    (forall i:int :: forall j:int ::
        0 <= i < j < 5 ==> s[i + j] == s[i] == s[j]) // not work?
}

predicate P1(s:seq<int>)
    requires 10 < |s|
{
    addition_bound_instance ();
    // addition_bound (0, 5); // not work
    assume (forall i, j {:trigger i + j} :: i + j < 10 ==> i + j < |s|);

    (forall i:int, j: int {:trigger s[i], s[j]} ::
        0 <= i < j < 5 ==> s[i + j] == s[i]+s[j])
}

predicate P2(s:seq<int>)
    requires 10 < |s|
{
    addition_bound_instance ();
    assume (forall i, j {:trigger i + j} :: i + j < 10 ==> i + j < |s|);
    (forall i:int, j: int ::
        0 <= i < j < 5 ==> s[i + j] == s[i]+s[j])
}