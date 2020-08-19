ADT_LOG_DIR=./Logs_adt
ORI_LOG_DIR=./Logs_orig

mkdir -p $ORI_LOG_DIR
dafny /compile:0 DLL-int.dfy /restartProver /trace /timeLimit:100 > $ORI_LOG_DIR/CP3-S0.trace;
echo "CP3, no Seed, done";
for i in `seq 1 5`; do
    dafny /compile:0 DLL-int.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:random-seed=${i}00 > $ORI_LOG_DIR/CP3-S${i}00.trace;
    echo "CP3, Seed${i}00, done";
done
echo "Original, CP3, done";
dafny /compile:0 DLL-int.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:smt.CASE_SPLIT=1 > $ORI_LOG_DIR/CP1-S0.trace;
echo "CP1, no Seed, done";
for i in `seq 1 5`; do
    dafny /compile:0 DLL-int.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.CASE_SPLIT=1 > $ORI_LOG_DIR/CP1-S${i}00.trace;
    echo "CP1, Seed${i}00, done";
done
echo "Original, CP1, done";

mkdir -p $ADT_LOG_DIR
dafny /compile:0 DLL-ADT-short-module.dfy /restartProver /trace /timeLimit:100 > $ADT_LOG_DIR/CP3-S0.trace;
echo "CP3, no Seed, done";
for i in `seq 1 5`; do
    dafny /compile:0 DLL-ADT-short-module.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:random-seed=${i}00 > $ADT_LOG_DIR/CP3-S${i}00.trace;
    echo "CP3, Seed${i}00, done";
done
echo "ADT, CP3, done";
dafny /compile:0 DLL-ADT-short-module.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:smt.CASE_SPLIT=1 > $ADT_LOG_DIR/CP1-S0.trace;
echo "CP1, no Seed, done";
for i in `seq 1 5`; do
    dafny /compile:0 DLL-ADT-short-module.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.CASE_SPLIT=1 > $ADT_LOG_DIR/CP1-S${i}00.trace;
    echo "CP1, Seed${i}00, done";
done
echo "ADT, CP1, done";