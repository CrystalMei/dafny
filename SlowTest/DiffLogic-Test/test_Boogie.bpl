
function {:inline} LitInt(x: int) : int
{
  x
}

procedure Impl$$_module.__default.myAdd(a#0: int, b#0: int) returns ($_reverifyPost: bool);
  // free requires 0 == $FunctionContextHeight;
  // modifies $Heap, $Tick;
  // // frame condition: object granularity
  // free ensures (forall $o: ref :: 
  //   { $Heap[$o] } 
  //   $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // // boilerplate
  // free ensures $HeapSucc(old($Heap), $Heap);

implementation Impl$$_module.__default.myAdd(a#0: int, b#0: int) returns ($_reverifyPost: bool)
{
    // var $_Frame: <beta>[ref,Field beta]bool;

    //   // AddMethodImpl: myAdd, Impl$$_module.__default.myAdd
    //   $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
    //     $o != null && read($Heap, $o, alloc) ==> false);
    //   assume {:captureState "test_Dafny.dfy(2,4): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- test_Dafny.dfy(2,7)
    if (a#0 == LitInt(10))
    {
    }

    if (a#0 == LitInt(10) && b#0 == LitInt(11))
    {
    }

    assume true;
    assert {:subsumption 0} a#0 == LitInt(10) && b#0 == LitInt(11) ==> a#0 + b#0 == LitInt(21);
    assume a#0 == LitInt(10) && b#0 == LitInt(11) ==> a#0 + b#0 == LitInt(21);
}


