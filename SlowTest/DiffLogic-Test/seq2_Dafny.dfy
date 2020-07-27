// dafny/Test/dafny4/git-issue96.dfy

function method add(x: int, y: int) : int { x + y }

lemma addition_bound_instance ()
    ensures forall i, j {:trigger add(i, j)} :: 0 <= i && 0 <= j ==> 0 <= add(i, j)
    ensures forall i, j {:trigger add(i, j)} :: i < 5 && j < 5 ==> add(i, j) < 10

lemma addition_bound (i: int, j: int, l: int, h: int)
    ensures l <= i && l <= j ==> l + l <= add(i, j)
    ensures i < h && j < h ==> add(i, j) < h + h

// predicate P(s:seq<int>)
//     requires 10 < |s|
// {
//     addition_bound_instance ();
//     (forall i:int {:trigger s[i]} :: forall j:int {:trigger s[j]} ::
//         0 <= i < j < 5 ==> s[add(i, j)] == s[i] == s[j])
// }

// predicate P0(s:seq<int>)
//     requires 10 < |s|
// {
//     addition_bound_instance ();
//     (forall i:int :: forall j:int ::
//         0 <= i < j < 5 ==> s[add(i, j)] == s[i] == s[j])
// }

// predicate P1(s:seq<int>)
method P1(s:seq<int>) returns (b: bool)
    requires 10 < |s|
{
    forall i: int, j: int | 0 <= i < j < 5
        ensures 0 <= add(i, j)
        ensures add(i, j) < 10
        {
            // addition_bound_instance ();
            addition_bound(i, j, 0, 5); // doesn't work
        }

    // (forall i:int, j: int {:trigger s[i], s[j]} :: 0 <= i < j < 5 ==> s[add(i, j)] == s[i]+s[j])
    b := (forall i:int, j: int {:trigger s[i], s[j]} :: 0 <= i < j < 5 ==> s[add(i, j)] == s[i]+s[j]);
}

// predicate P2(s:seq<int>)
//     requires 10 < |s|
// {
//     addition_bound_instance ();
//     (forall i:int, j: int ::
//         0 <= i < j < 5 ==> s[add(i, j)] == s[i]+s[j])
// }