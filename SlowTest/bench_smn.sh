##### DLL #####
LOG_DIR=./Logs_SMN_8.20
ADT_5_LOG_DIR=./Logs_SMN_8.20/Logs_adt_4.8.5
ORI_5_LOG_DIR=./Logs_SMN_8.20/Logs_orig_4.8.5
ADT_9_LOG_DIR=./Logs_SMN_8.20/Logs_adt_4.8.9
ORI_9_LOG_DIR=./Logs_SMN_8.20/Logs_orig_4.8.9
ADT_8_LOG_DIR=./Logs_SMN_8.20/Logs_adt_4.8.8
ORI_8_LOG_DIR=./Logs_SMN_8.20/Logs_orig_4.8.8
seeds=`seq 1 30`

# mkdir -p $LOG_DIR
# # 4.8.5 original
# mkdir -p $ORI_5_LOG_DIR
# dafny /compile:0 SMN-orig.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.5/bin/z3" > $ORI_5_LOG_DIR/CP3-S0.trace;
# echo "4.8.5, CP3, no Seed, done";
# for i in $seeds; do
#     dafny /compile:0 SMN-orig.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:random-seed=${i}00 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.5/bin/z3" > $ORI_5_LOG_DIR/CP3-S${i}00.trace;
#     echo "4.8.5, CP3, Seed${i}00, done";
# done
# echo "4.8.5, Original, CP3, done";

# dafny /compile:0 SMN-orig.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:smt.CASE_SPLIT=1 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.5/bin/z3" > $ORI_5_LOG_DIR/CP1-S0.trace;
# echo "4.8.5, CP1, no Seed, done";
# for i in $seeds; do
#     dafny /compile:0 SMN-orig.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.CASE_SPLIT=1 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.5/bin/z3" > $ORI_5_LOG_DIR/CP1-S${i}00.trace;
#     echo "4.8.5, CP1, Seed${i}00, done";
# done
# echo "4.8.5, Original, CP1, done";

# # 4.8.5 ADT
# mkdir -p $ADT_5_LOG_DIR
# dafny /compile:0 SMN-ADT-module-ContLen-Add.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.5/bin/z3" > $ADT_5_LOG_DIR/CP3-S0.trace;
# echo "4.8.5, CP3, no Seed, done";
# for i in $seeds; do
#     dafny /compile:0 SMN-ADT-module-ContLen-Add.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:random-seed=${i}00 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.5/bin/z3" > $ADT_5_LOG_DIR/CP3-S${i}00.trace;
#     echo "4.8.5, CP3, Seed${i}00, done";
# done
# echo "4.8.5, ADT, CP3, done";

# dafny /compile:0  /restartProver /trace /timeLimit:100 /proverOpt:O:smt.CASE_SPLIT=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.5/bin/z3" > $ADT_5_LOG_DIR/CP1-S0.trace;
# echo "4.8.5, CP1, no Seed, done";
# for i in $seeds; do
#     dafny /compile:0 SMN-ADT-module-ContLen-Add.dfy  /restartProver /trace /timeLimit:100 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.CASE_SPLIT=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.5/bin/z3" > $ADT_5_LOG_DIR/CP1-S${i}00.trace;
#     echo "4.8.5, CP1, Seed${i}00, done";
# done
# echo "4.8.5, ADT, CP1, done";


# 4.8.9 original
mkdir -p $ORI_9_LOG_DIR
dafny /compile:0 SMN-orig.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.9/bin/z3" > $ORI_9_LOG_DIR/CP3-S0.trace;
echo "4.8.9, CP3, no Seed, done";
for i in $seeds; do
    dafny /compile:0 SMN-orig.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:random-seed=${i}00 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.9/bin/z3" > $ORI_9_LOG_DIR/CP3-S${i}00.trace;
    echo "4.8.9, CP3, Seed${i}00, done";
done
echo "4.8.9, Original, CP3, done";

dafny /compile:0 SMN-orig.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:smt.CASE_SPLIT=1 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.9/bin/z3" > $ORI_9_LOG_DIR/CP1-S0.trace;
echo "4.8.9, CP1, no Seed, done";
for i in $seeds; do
    dafny /compile:0 SMN-orig.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.CASE_SPLIT=1 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.9/bin/z3" > $ORI_9_LOG_DIR/CP1-S${i}00.trace;
    echo "4.8.9, CP1, Seed${i}00, done";
done
echo "4.8.9, Original, CP1, done";

# 4.8.9 ADT
mkdir -p $ADT_9_LOG_DIR
dafny /compile:0 SMN-ADT-module-ContLen-Add.dfy  /restartProver /trace /timeLimit:100 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.9/bin/z3" > $ADT_9_LOG_DIR/CP3-S0.trace;
echo "4.8.9, CP3, no Seed, done";
for i in $seeds; do
    dafny /compile:0 SMN-ADT-module-ContLen-Add.dfy  /restartProver /trace /timeLimit:100 /proverOpt:O:random-seed=${i}00 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.9/bin/z3" > $ADT_9_LOG_DIR/CP3-S${i}00.trace;
    echo "4.8.9, CP3, Seed${i}00, done";
done
echo "4.8.9, ADT, CP3, done";

dafny /compile:0 DLL-ADT-short-module_CS1.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:smt.CASE_SPLIT=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.9/bin/z3" > $ADT_9_LOG_DIR/CP1-S0.trace;
echo "4.8.9, CP1, no Seed, done";
for i in $seeds; do
    dafny /compile:0 DLL-ADT-short-module_CS1.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.CASE_SPLIT=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.9/bin/z3" > $ADT_9_LOG_DIR/CP1-S${i}00.trace;
    echo "4.8.9, CP1, Seed${i}00, done";
done
echo "4.8.9, ADT, CP1, done";


# 4.8.8 original
mkdir -p $ORI_8_LOG_DIR
dafny /compile:0 SMN-orig.dfy /restartProver /trace /timeLimit:100 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.8/bin/z3" > $ORI_8_LOG_DIR/CP3-S0.trace;
echo "4.8.8, CP3, no Seed, done";
for i in $seeds; do
    dafny /compile:0 SMN-orig.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:random-seed=${i}00 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.8/bin/z3" > $ORI_8_LOG_DIR/CP3-S${i}00.trace;
    echo "4.8.8, CP3, Seed${i}00, done";
done
echo "4.8.8, Original, CP3, done";

dafny /compile:0 SMN-orig.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:smt.CASE_SPLIT=1 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.8/bin/z3" > $ORI_8_LOG_DIR/CP1-S0.trace;
echo "4.8.8, CP1, no Seed, done";
for i in $seeds; do
    dafny /compile:0 SMN-orig.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.CASE_SPLIT=1 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.8/bin/z3" > $ORI_8_LOG_DIR/CP1-S${i}00.trace;
    echo "4.8.8, CP1, Seed${i}00, done";
done
echo "4.8.8, Original, CP1, done";

# 4.8.8 ADT
mkdir -p $ADT_8_LOG_DIR
dafny /compile:0 SMN-ADT-module-ContLen-Add.dfy  /restartProver /trace /timeLimit:100 /errorLimit:1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.8/bin/z3" > $ADT_8_LOG_DIR/CP3-S0.trace;
echo "4.8.8, CP3, no Seed, done";
for i in $seeds; do
    dafny /compile:0 SMN-ADT-module-ContLen-Add.dfy  /restartProver /trace /timeLimit:100 /proverOpt:O:random-seed=${i}00 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.8/bin/z3" > $ADT_8_LOG_DIR/CP3-S${i}00.trace;
    echo "4.8.8, CP3, Seed${i}00, done";
done
echo "4.8.8, ADT, CP3, done";

dafny /compile:0 SMN-ADT-module-ContLen-Add.dfy  /restartProver /trace /timeLimit:100 /proverOpt:O:smt.CASE_SPLIT=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.8/bin/z3" > $ADT_8_LOG_DIR/CP1-S0.trace;
echo "4.8.8, CP1, no Seed, done";
for i in $seeds; do
    dafny /compile:0 SMN-ADT-module-ContLen-Add.dfy  /restartProver /trace /timeLimit:100 /proverOpt:O:random-seed=${i}00 /proverOpt:O:smt.CASE_SPLIT=1 /z3exe:"/home/jmhu/MSRintern/dafny/Binaries/z3-4.8.8/bin/z3" > $ADT_8_LOG_DIR/CP1-S${i}00.trace;
    echo "4.8.8, CP1, Seed${i}00, done";
done
echo "4.8.8, ADT, CP1, done";
