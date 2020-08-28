Readme

# Test Cases Information
### Benchmark
* bench-dll.sh: benchmark for Doubly Linked List case
* bench-smn.sh: benchmark for Smallest Missing Number case
* dump_dll.py: performance figure generation for DLL case
* dump_smn.py: performance figure generation for SMN case
* Makefile: benchmark for slow test cases (old version)

### ADT Module
* ADT-int.dfy: abstract integer types, operations, and lemmas
* ADT-seq.dfy: abstract sequence types, operations, and lemmas
* ADT-seq2.dfy: old version of abstract sequence types, operations, and lemmas

### Sequence Operations
* Seq-ADT-ADT.dfy, Seq-DT-ADT.dfy: verification for several abstract-data-type sequence operations

### Doubly Linked List
* DLL-orig.dfy: Doubly-Linked-List original program
* DLL-int.dfy: Doubly-Linked-List original program (integer version)
* DLL-ADT-module.dfy: Doubly-Linked-List abstract-data-type program with ADT module
* DLL-ADT-module_CS1.dfy: Doubly-Linked-List abstract-data-type program (assertion modified, see Problem below)
* DLL-int-noLambda.dfy: Doubly-Linked-List program (without lambda)
* DLL-int-noSeqCon.dfy: Doubly-Linked-List program (without sequence concatenation)

### Smallest Missing Number
* SMN-orig.dfy: Smallest-Missing-Number original program
* SMN-ADt-module.dfy: Smallest-Missing-Number abstract-data-type program with ADT module
* SMN-ADT-ListContent.dfy: Smallest-Missing-Number abstract-data-type program (ADT list content but integer list index)
* SMN-ADT-ListConLen-Add.dfy: Smallest-Missing-Number abstract-data-type program (ADT list content and adt list index; addition supported)
* SMN-ADT-ListConLen-Inc.dfy: Smallest-Missing-Number abstract-data-type program (ADT list content and adt list index; Increment supported)

### Vector Update
* VectorUpdate-orig.dfy: Vector-Update original program (array version)
* VectorUpdate-seq.dfy: Vector-Update original program (sequence version)
* VectorUpdate-ADT.dfy: Vector-Update abstract-data-type program
* VectorUpdate-ADT-module.dfy: Vector-Update abstract-data-type program with ADT module

### Other Tests
* BinaryTree
* Composite
* FloydCycle
* QuickSort
* LetExpr
* ListContents
* MoreInduction
* NoTypeArgs
* Queue
* Rippling
* SnapshotableTrees
* UnionFind

# Subdirectory
### OptionInfo
z3 and dafny options

### DiffLogic-Test
DLL and SMN programs for difference logic solvers

#### Benchmark
* bench_dll2.sh: benchmark for Doubly Linked List case
* bench_dll.sh: benchmark for DLL case (dense diff logic only)
* dump_dll.py: performance figure generation for DLL case
* Makefile: benchmark for DLL case (old version)

#### Test cases
* DLL_Dafny_WDL.dfy: verified with weakened diff logic with equation substitution (working version)
* DLL_Dafny_WDL2.dfy: verified with weakened diff logic with weight relaxation (working version)
* DLL_Dafny_WDL_old*.dfy: old version for weakened diff logic solver
* DLL_Dafny_SDL.dfy: verified with sparse diff logic solver
* DLL_Dafny_DDL.dfy: verified with dense diff logic solver
* DLL_Dafny_Original*.dfy: original DLL program with small modification
* SMN_Dafny*.dfy: SMN program (not tested)
* VU_Dafny.dfy: VectorUpdate program (not tested)
* Test/: all test files for various reasons

### NoArith-Test
DLL and SMN programs for solver 0 (no-arithmetic solver)

### Figures
Figures in the summary paper

### NoLongerNeedTest
OLD slow test cases


# Problems
### DLL-int.dfy: original program
* z3 4.8.9 Case-Split 3, InsertAfter(): require assertion (L279: assert Index(l, p) == index) to be verified successfully
* z3 4.8.9 Case-Split 1, InsertBefore(): require assertion (L313: assert index' == IndexHi(l, p)) to be verified successfully
* z3 4.8.9 Case-Split 1, add extra triggers might fail verification

### DLL-ADT-module.dfy: abstract-data-type version
* z3 4.8.5 Case-Split 1, BuildFreeStack(): timeout on loop invariant
* z3 4.8.9 InsertBefore(): assertion (L565) is required for Case-Split 3, but not required for Case-Split 1 (see comments in file)

### DLL-int-noLambda.dfy: no lambda version
* z3 4.8.5 Case-Split 1, InsertAfter_SeqInit(): verified with one trigger (adding extra trigger {:trigger g[x]} fails verification)
* z3 4.8.9 Case-Split 3: tried with multiple triggers and verified
