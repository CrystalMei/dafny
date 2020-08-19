Solver3_Log=./Logs_solver3
Default_Log=./Logs_default

mkdir -p $Default_Log
dafny /compile:0 DLL_Dafny_DDL.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 > $Default_Log/CP3-S0.trace;
echo "CP3, no Seed, done";
for i in `seq 1 5`; do
    dafny /compile:0 DLL_Dafny_DDL.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 > $Default_Log/CP3-S${i}00.trace;
    echo "CP3, Seed${i}00, done";
done
echo "Original, CP3, done";
dafny /compile:0 DLL_Dafny_DDL.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:smt.CASE_SPLIT=1 > $Default_Log/CP1-S0.trace;
echo "CP1, no Seed, done";
for i in `seq 1 5`; do
    dafny /compile:0 DLL_Dafny_DDL.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.CASE_SPLIT=1 > $Default_Log/CP1-S${i}00.trace;
    echo "CP1, Seed${i}00, done";
done
echo "Original, CP1, done";

mkdir -p $Solver3_Log
dafny /compile:0 DLL_Dafny_DDL.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:smt.arith.solver=3 > $Solver3_Log/CP3-S0.trace;
echo "CP3, no Seed, done";
for i in `seq 1 5`; do
    dafny /compile:0 DLL_Dafny_DDL.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.arith.solver=3 > $Solver3_Log/CP3-S${i}00.trace;
    echo "CP3, Seed${i}00, done";
done
echo "DDL, CP3, done";
dafny /compile:0 DLL_Dafny_DDL.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:smt.CASE_SPLIT=1 /proverOpt:O:smt.arith.solver=3 > $Solver3_Log/CP1-S0.trace;
echo "CP1, no Seed, done";
for i in `seq 1 5`; do
    dafny /compile:0 DLL_Dafny_DDL.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.arith.solver=3 /proverOpt:O:smt.CASE_SPLIT=1 > $Solver3_Log/CP1-S${i}00.trace;
    echo "CP1, Seed${i}00, done";
done
echo "DDL, CP1, done";