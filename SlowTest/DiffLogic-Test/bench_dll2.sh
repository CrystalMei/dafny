Solver1_Log=./Logs_solver1
Solver3_Log=./Logs_solver3
Solver7_Log=./Logs_solver7
Default_Log=./Logs_default
Default5_Log=./Logs_default5
Default8_Log=./Logs_default8
Default9_Log=./Logs_default9
seeds=`seq 1 30`

# 4.8.5
mkdir -p $Default5_Log
dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.5/bin/z3" > $Default5_Log/CP3-S0.trace;
echo "CP3, no Seed, done";
for i in $seeds; do
    dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.5/bin/z3" > $Default5_Log/CP3-S${i}00.trace;
    echo "CP3, Seed${i}00, done";
done
echo "Original 4.8.5, CP3, done";

dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:smt.CASE_SPLIT=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.5/bin/z3" > $Default5_Log/CP1-S0.trace;
echo "CP1, no Seed, done";
for i in $seeds; do
    dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.CASE_SPLIT=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.5/bin/z3" > $Default5_Log/CP1-S${i}00.trace;
    echo "CP1, Seed${i}00, done";
done
echo "Original 4.8.5, CP1, done";

# modified default solver
mkdir -p $Default_Log
dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-solver7/bin/z3" > $Default_Log/CP3-S0.trace;
echo "CP3, no Seed, done";
for i in $seeds; do
    dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-solver7/bin/z3" > $Default_Log/CP3-S${i}00.trace;
    echo "CP3, Seed${i}00, done";
done
echo "Original, CP3, done";

dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:smt.CASE_SPLIT=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-solver7/bin/z3" > $Default_Log/CP1-S0.trace;
echo "CP1, no Seed, done";
for i in $seeds; do
    dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.CASE_SPLIT=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-solver7/bin/z3" > $Default_Log/CP1-S${i}00.trace;
    echo "CP1, Seed${i}00, done";
done
echo "Original, CP1, done";


# modified solver 1
mkdir -p $Solver1_Log
dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:smt.arith.solver=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-solver7/bin/z3" > $Solver1_Log/CP3-S0.trace;
echo "CP3, no Seed, done";
for i in $seeds; do
    dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.arith.solver=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-solver7/bin/z3" > $Solver1_Log/CP3-S${i}00.trace;
    echo "CP3, Seed${i}00, done";
done
echo "SDL, CP3, done";
dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:smt.CASE_SPLIT=1 /proverOpt:O:smt.arith.solver=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-solver7/bin/z3" > $Solver1_Log/CP1-S0.trace;
echo "CP1, no Seed, done";
for i in $seeds; do
    dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.arith.solver=1 /proverOpt:O:smt.CASE_SPLIT=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-solver7/bin/z3" > $Solver1_Log/CP1-S${i}00.trace;
    echo "CP1, Seed${i}00, done";
done
echo "SDL, CP1, done";


# modified solver 7
mkdir -p $Solver7_Log
dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:smt.arith.solver=7 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-solver7/bin/z3" > $Solver7_Log/CP3-S0.trace;
echo "CP3, no Seed, done";
for i in $seeds; do
    dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.arith.solver=7 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-solver7/bin/z3" > $Solver7_Log/CP3-S${i}00.trace;
    echo "CP3, Seed${i}00, done";
done
echo "WDL, CP3, done";
dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:smt.CASE_SPLIT=1 /proverOpt:O:smt.arith.solver=7 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-solver7/bin/z3" > $Solver7_Log/CP1-S0.trace;
echo "CP1, no Seed, done";
for i in $seeds; do
    dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.arith.solver=7 /proverOpt:O:smt.CASE_SPLIT=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-solver7/bin/z3" > $Solver7_Log/CP1-S${i}00.trace;
    echo "CP1, Seed${i}00, done";
done
echo "WDL, CP1, done";


# modified solver 3
mkdir -p $Solver3_Log
dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:smt.arith.solver=3 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-solver7/bin/z3" > $Solver3_Log/CP3-S0.trace;
echo "CP3, no Seed, done";
for i in $seeds; do
    dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.arith.solver=3 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-solver7/bin/z3" > $Solver3_Log/CP3-S${i}00.trace;
    echo "CP3, Seed${i}00, done";
done
echo "DDL, CP3, done";
dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:smt.CASE_SPLIT=1 /proverOpt:O:smt.arith.solver=3 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-solver7/bin/z3" > $Solver3_Log/CP1-S0.trace;
echo "CP1, no Seed, done";
for i in $seeds; do
    dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.arith.solver=3 /proverOpt:O:smt.CASE_SPLIT=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-solver7/bin/z3" > $Solver3_Log/CP1-S${i}00.trace;
    echo "CP1, Seed${i}00, done";
done
echo "DDL, CP1, done";



# # 4.8.8
# mkdir -p $Default8_Log
# dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.8/bin/z3" > $Default8_Log/CP3-S0.trace;
# echo "CP3, no Seed, done";
# for i in $seeds; do
#     dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.8/bin/z3" > $Default8_Log/CP3-S${i}00.trace;
#     echo "CP3, Seed${i}00, done";
# done
# echo "Original 4.8.8, CP3, done";

# dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:smt.CASE_SPLIT=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.8/bin/z3" > $Default8_Log/CP1-S0.trace;
# echo "CP1, no Seed, done";
# for i in $seeds; do
#     dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.CASE_SPLIT=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.8/bin/z3" > $Default8_Log/CP1-S${i}00.trace;
#     echo "CP1, Seed${i}00, done";
# done
# echo "Original 4.8.8, CP1, done";


# # 4.8.9
# mkdir -p $Default9_Log
# dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.9/bin/z3" > $Default9_Log/CP3-S0.trace;
# echo "CP3, no Seed, done";
# for i in $seeds; do
#     dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.9/bin/z3" > $Default9_Log/CP3-S${i}00.trace;
#     echo "CP3, Seed${i}00, done";
# done
# echo "Original 4.8.9, CP3, done";

# dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:smt.CASE_SPLIT=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.9/bin/z3" > $Default9_Log/CP1-S0.trace;
# echo "CP1, no Seed, done";
# for i in $seeds; do
#     dafny /compile:0 DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.CASE_SPLIT=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.9/bin/z3" > $Default9_Log/CP1-S${i}00.trace;
#     echo "CP1, Seed${i}00, done";
# done
# echo "Original 4.8.9, CP1, done";