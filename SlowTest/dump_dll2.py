#!/usr/bin/env python3

import os
import glob
import re
import sys
import math

TIMEOUT = 100
# use cases and their directory names
tests = [
  "CP3-4.8.5", "CP1-4.8.5", "CP3-4.8.9", "CP1-4.8.9",
  "noSeqCon-CP3-4.8.5", "noSeqCon-CP1-4.8.5", "noSeqCon-CP3-4.8.9", "noSeqCon-CP1-4.8.9",
  "nolambda-CP3-4.8.5", "nolambda-CP1-4.8.5", "nolambda-CP3-4.8.9", "nolambda-CP1-4.8.9"
]

loc_orig_5 = os.path.join('Logs_DLL_8.20', 'Logs_orig_4.8.5', '*.trace')
loc_orig_9 = os.path.join('Logs_DLL_8.20', 'Logs_orig_4.8.9', '*.trace')
loc_noseqcon_5 = os.path.join('Logs_DLL_8.20', 'Logs_noseqcon_4.8.5', '*.trace')
loc_noseqcon_9 = os.path.join('Logs_DLL_8.20', 'Logs_noseqcon_4.8.9', '*.trace')
loc_nolambda_5 = os.path.join('Logs_DLL_8.20', 'Logs_nolambda_4.8.5', '*.trace')
loc_nolambda_9 = os.path.join('Logs_DLL_8.20', 'Logs_nolambda_4.8.9', '*.trace')
file_orig_5 = glob.glob(loc_orig_5)
file_orig_9 = glob.glob(loc_orig_9)
file_noseqcon_5 = glob.glob(loc_noseqcon_5)
file_noseqcon_9 = glob.glob(loc_noseqcon_9)
file_nolambda_5 = glob.glob(loc_nolambda_5)
file_nolambda_9 = glob.glob(loc_nolambda_9)

allinfo_Expand = {}
allinfo_Remove = {}
allinfo_InsertAfter = {}
allinfo_InsertBefore = {}

def get_time (files, index):
    for f in files:
        outfile = open(f, 'r')
        data = outfile.readlines()
        outfile.close()
        for i in range(0, len(data)):
            if 'Verifying Impl$$_module.__default.Expand ...' in data[i]:
                time = re.findall("\[([0-9.]*) s, ([0-9.]*) proof obligations\]  ([a-z]+)", data[i + 1])
                if len(time) > 0:
                    if time[0][2] == "verified":
                        if 'CP3' in f:
                            allinfo_Expand[tests[index]] = allinfo_Expand.get(tests[index], [])
                            allinfo_Expand[tests[index]] += [float(time[0][0])]
                        else:
                            allinfo_Expand[tests[index+1]] = allinfo_Expand.get(tests[index+1], [])
                            allinfo_Expand[tests[index+1]] += [float(time[0][0])]
                    else:
                        if time[0][2] == "timed":
                            if 'CP3' in f:
                                allinfo_Expand[tests[index]] = allinfo_Expand.get(tests[index], [])
                                allinfo_Expand[tests[index]] += [float(TIMEOUT)]
                            else:
                                allinfo_Expand[tests[index+1]] = allinfo_Expand.get(tests[index+1], [])
                                allinfo_Expand[tests[index+1]] += [float(TIMEOUT)]
                        else:
                            allinfo_Expand[tests[index]] = allinfo_Expand.get(tests[index], [])
                            allinfo_Expand[tests[index+1]] = allinfo_Expand.get(tests[index+1], [])

            
            if 'Verifying Impl$$_module.__default.Remove ...' in data[i]:
                time = re.findall("\[([0-9.]*) s, ([0-9.]*) proof obligations\]  ([a-z]+)", data[i + 1])
                if len(time) > 0:
                    if time[0][2] == "verified":
                        if 'CP3' in f:
                            allinfo_Remove[tests[index]] = allinfo_Remove.get(tests[index], [])
                            allinfo_Remove[tests[index]] += [float(time[0][0])]
                        else:
                            allinfo_Remove[tests[index+1]] = allinfo_Remove.get(tests[index+1], [])
                            allinfo_Remove[tests[index+1]] += [float(time[0][0])] 
                    else:
                        if time[0][2] == "timed":
                            if 'CP3' in f:
                                allinfo_Remove[tests[index]] = allinfo_Remove.get(tests[index], [])
                                allinfo_Remove[tests[index]] += [float(TIMEOUT)]
                            else:
                                allinfo_Remove[tests[index+1]] = allinfo_Remove.get(tests[index+1], [])
                                allinfo_Remove[tests[index+1]] += [float(TIMEOUT)]
                        else:
                            allinfo_Remove[tests[index]] = allinfo_Remove.get(tests[index], [])
                            allinfo_Remove[tests[index+1]] = allinfo_Remove.get(tests[index+1], [])


            if 'Verifying Impl$$_module.__default.InsertAfter ...' in data[i]:
                time = re.findall("\[([0-9.]*) s, ([0-9.]*) proof obligations\]  ([a-z]+)", data[i + 1])
                if len(time) > 0:
                    if time[0][2] == "verified":
                        if 'CP3' in f:
                            allinfo_InsertAfter[tests[index]] = allinfo_InsertAfter.get(tests[index], [])
                            allinfo_InsertAfter[tests[index]] += [float(time[0][0])]
                        else:
                            allinfo_InsertAfter[tests[index+1]] = allinfo_InsertAfter.get(tests[index+1], [])
                            allinfo_InsertAfter[tests[index+1]] += [float(time[0][0])]
                    else:
                        if time[0][2] == "timed":
                            if 'CP3' in f:
                                allinfo_InsertAfter[tests[index]] = allinfo_InsertAfter.get(tests[index], [])
                                allinfo_InsertAfter[tests[index]] += [float(TIMEOUT)]
                            else:
                                allinfo_InsertAfter[tests[index+1]] = allinfo_InsertAfter.get(tests[index+1], [])
                                allinfo_InsertAfter[tests[index+1]] += [float(TIMEOUT)]
                        else:
                            allinfo_InsertAfter[tests[index]] = allinfo_InsertAfter.get(tests[index], [])
                            allinfo_InsertAfter[tests[index+1]] = allinfo_InsertAfter.get(tests[index+1], [])

            if 'Verifying Impl$$_module.__default.InsertBefore ...' in data[i]:
                time = re.findall("\[([0-9.]*) s, ([0-9.]*) proof obligations\]  ([a-z]+)", data[i + 1])
                if len(time) > 0:
                    if time[0][2] == "verified":
                        if 'CP3' in f:
                            allinfo_InsertBefore[tests[index]] = allinfo_InsertBefore.get(tests[index], [])
                            allinfo_InsertBefore[tests[index]] += [float(time[0][0])]
                        else:
                            allinfo_InsertBefore[tests[index+1]] = allinfo_InsertBefore.get(tests[index+1], [])
                            allinfo_InsertBefore[tests[index+1]] += [float(time[0][0])]
                    else:
                        if time[0][2] == "timed":
                            if 'CP3' in f:
                                allinfo_InsertBefore[tests[index]] = allinfo_InsertBefore.get(tests[index], [])
                                allinfo_InsertBefore[tests[index]] += [float(TIMEOUT)]
                            else:
                                allinfo_InsertBefore[tests[index+1]] = allinfo_InsertBefore.get(tests[index+1], [])
                                allinfo_InsertBefore[tests[index+1]] += [float(TIMEOUT)]
                        else:
                            allinfo_InsertBefore[tests[index]] = allinfo_InsertBefore.get(tests[index], [])
                            allinfo_InsertBefore[tests[index+1]] = allinfo_InsertBefore.get(tests[index+1], [])

get_time(file_orig_5, 0)
get_time(file_orig_9, 2)
get_time(file_noseqcon_5, 4)
get_time(file_noseqcon_9, 6)
get_time(file_nolambda_5, 8)
get_time(file_nolambda_9, 10)

# print(allinfo_Expand)
# print(allinfo_Remove)
# print(allinfo_InsertAfter)
# print(allinfo_InsertBefore)

# print a CSV
def show_csv(allinfo, info):
  for test in tests:
    if test in allinfo:
        times = allinfo[test]
        print(test + ", " + info),
        for i in times:
            print(", " + str(i)),
        print ("\n"),

# show_csv(allinfo_Expand, "Expand")
# show_csv(allinfo_Remove, "Remove")
# show_csv(allinfo_InsertAfter, "InsertAfter")
# show_csv(allinfo_InsertBefore, "InsertBefore")

import numpy as np
import matplotlib
import matplotlib.pyplot as plt
matplotlib.rcParams.update({'font.size': 20})

Expand_cp3_5 = np.array(allinfo_Expand[tests[0]])
Expand_cp1_5 = np.array(allinfo_Expand[tests[1]])
Expand_cp3_9 = np.array(allinfo_Expand[tests[2]])
Expand_cp1_9 = np.array(allinfo_Expand[tests[3]])
Expand_noseqcon_cp3_5 = np.array(allinfo_Expand[tests[4]])
Expand_noseqcon_cp1_5 = np.array(allinfo_Expand[tests[5]])
Expand_noseqcon_cp3_9 = np.array(allinfo_Expand[tests[6]])
Expand_noseqcon_cp1_9 = np.array(allinfo_Expand[tests[7]])
Expand_nolambda_cp3_5 = np.array(allinfo_Expand[tests[8]])
Expand_nolambda_cp1_5 = np.array(allinfo_Expand[tests[9]])
Expand_nolambda_cp3_9 = np.array(allinfo_Expand[tests[10]])
Expand_nolambda_cp1_9 = np.array(allinfo_Expand[tests[11]])

Expand_cp3_5_mean = np.mean(Expand_cp3_5)
Expand_cp3_5_std = np.std(Expand_cp3_5)
Expand_cp1_5_mean = np.mean(Expand_cp1_5)
Expand_cp1_5_std = np.std(Expand_cp1_5)
Expand_cp3_9_mean = np.mean(Expand_cp3_9)
Expand_cp3_9_std = np.std(Expand_cp3_9)
Expand_cp1_9_mean = np.mean(Expand_cp1_9)
Expand_cp1_9_std = np.std(Expand_cp1_9)

Expand_noseqcon_cp3_5_mean = np.mean(Expand_noseqcon_cp3_5)
Expand_noseqcon_cp3_5_std = np.std(Expand_noseqcon_cp3_5)
Expand_noseqcon_cp1_5_mean = np.mean(Expand_noseqcon_cp1_5)
Expand_noseqcon_cp1_5_std = np.std(Expand_noseqcon_cp1_5)
Expand_noseqcon_cp3_9_mean = np.mean(Expand_noseqcon_cp3_9)
Expand_noseqcon_cp3_9_std = np.std(Expand_noseqcon_cp3_9)
Expand_noseqcon_cp1_9_mean = np.mean(Expand_noseqcon_cp1_9)
Expand_noseqcon_cp1_9_std = np.std(Expand_noseqcon_cp1_9)

Expand_nolambda_cp3_5_mean = np.mean(Expand_nolambda_cp3_5)
Expand_nolambda_cp3_5_std = np.std(Expand_nolambda_cp3_5)
Expand_nolambda_cp1_5_mean = np.mean(Expand_nolambda_cp1_5)
Expand_nolambda_cp1_5_std = np.std(Expand_nolambda_cp1_5)
Expand_nolambda_cp3_9_mean = np.mean(Expand_nolambda_cp3_9)
Expand_nolambda_cp3_9_std = np.std(Expand_nolambda_cp3_9)
Expand_nolambda_cp1_9_mean = np.mean(Expand_nolambda_cp1_9)
Expand_nolambda_cp1_9_std = np.std(Expand_nolambda_cp1_9)

Remove_cp3_5 = np.array(allinfo_Remove[tests[0]])
Remove_cp1_5 = np.array(allinfo_Remove[tests[1]])
Remove_cp3_9 = np.array(allinfo_Remove[tests[2]])
Remove_cp1_9 = np.array(allinfo_Remove[tests[3]])
Remove_noseqcon_cp3_5 = np.array(allinfo_Remove[tests[4]])
Remove_noseqcon_cp1_5 = np.array(allinfo_Remove[tests[5]])
Remove_noseqcon_cp3_9 = np.array(allinfo_Remove[tests[6]])
Remove_noseqcon_cp1_9 = np.array(allinfo_Remove[tests[7]])
Remove_nolambda_cp3_5 = np.array(allinfo_Remove[tests[8]])
Remove_nolambda_cp1_5 = np.array(allinfo_Remove[tests[9]])
Remove_nolambda_cp3_9 = np.array(allinfo_Remove[tests[10]])
Remove_nolambda_cp1_9 = np.array(allinfo_Remove[tests[11]])

Remove_cp3_5_mean = np.mean(Remove_cp3_5)
Remove_cp3_5_std = np.std(Remove_cp3_5)
Remove_cp1_5_mean = np.mean(Remove_cp1_5)
Remove_cp1_5_std = np.std(Remove_cp1_5)
Remove_cp3_9_mean = np.mean(Remove_cp3_9)
Remove_cp3_9_std = np.std(Remove_cp3_9)
Remove_cp1_9_mean = np.mean(Remove_cp1_9)
Remove_cp1_9_std = np.std(Remove_cp1_9)

Remove_noseqcon_cp3_5_mean = np.mean(Remove_noseqcon_cp3_5)
Remove_noseqcon_cp3_5_std = np.std(Remove_noseqcon_cp3_5)
Remove_noseqcon_cp1_5_mean = np.mean(Remove_noseqcon_cp1_5)
Remove_noseqcon_cp1_5_std = np.std(Remove_noseqcon_cp1_5)
Remove_noseqcon_cp3_9_mean = np.mean(Remove_noseqcon_cp3_9)
Remove_noseqcon_cp3_9_std = np.std(Remove_noseqcon_cp3_9)
Remove_noseqcon_cp1_9_mean = np.mean(Remove_noseqcon_cp1_9)
Remove_noseqcon_cp1_9_std = np.std(Remove_noseqcon_cp1_9)

Remove_nolambda_cp3_5_mean = np.mean(Remove_nolambda_cp3_5)
Remove_nolambda_cp3_5_std = np.std(Remove_nolambda_cp3_5)
Remove_nolambda_cp1_5_mean = np.mean(Remove_nolambda_cp1_5)
Remove_nolambda_cp1_5_std = np.std(Remove_nolambda_cp1_5)
Remove_nolambda_cp3_9_mean = np.mean(Remove_nolambda_cp3_9)
Remove_nolambda_cp3_9_std = np.std(Remove_nolambda_cp3_9)
Remove_nolambda_cp1_9_mean = np.mean(Remove_nolambda_cp1_9)
Remove_nolambda_cp1_9_std = np.std(Remove_nolambda_cp1_9)


InsertAfter_cp3_5 = np.array(allinfo_InsertAfter[tests[0]])
InsertAfter_cp1_5 = np.array(allinfo_InsertAfter[tests[1]])
InsertAfter_cp3_9 = np.array(allinfo_InsertAfter[tests[2]])
InsertAfter_cp1_9 = np.array(allinfo_InsertAfter[tests[3]])
InsertAfter_noseqcon_cp3_5 = np.array(allinfo_InsertAfter[tests[4]])
InsertAfter_noseqcon_cp1_5 = np.array(allinfo_InsertAfter[tests[5]])
InsertAfter_noseqcon_cp3_9 = np.array(allinfo_InsertAfter[tests[6]])
InsertAfter_noseqcon_cp1_9 = np.array(allinfo_InsertAfter[tests[7]])
InsertAfter_nolambda_cp3_5 = np.array(allinfo_InsertAfter[tests[8]])
InsertAfter_nolambda_cp1_5 = np.array(allinfo_InsertAfter[tests[9]])
InsertAfter_nolambda_cp3_9 = np.array(allinfo_InsertAfter[tests[10]])
InsertAfter_nolambda_cp1_9 = np.array(allinfo_InsertAfter[tests[11]])

InsertAfter_cp3_5_mean = np.mean(InsertAfter_cp3_5)
InsertAfter_cp3_5_std = np.std(InsertAfter_cp3_5)
InsertAfter_cp1_5_mean = np.mean(InsertAfter_cp1_5)
InsertAfter_cp1_5_std = np.std(InsertAfter_cp1_5)
InsertAfter_cp3_9_mean = np.mean(InsertAfter_cp3_9)
InsertAfter_cp3_9_std = np.std(InsertAfter_cp3_9)
InsertAfter_cp1_9_mean = np.mean(InsertAfter_cp1_9)
InsertAfter_cp1_9_std = np.std(InsertAfter_cp1_9)

InsertAfter_noseqcon_cp3_5_mean = np.mean(InsertAfter_noseqcon_cp3_5)
InsertAfter_noseqcon_cp3_5_std = np.std(InsertAfter_noseqcon_cp3_5)
InsertAfter_noseqcon_cp1_5_mean = np.mean(InsertAfter_noseqcon_cp1_5)
InsertAfter_noseqcon_cp1_5_std = np.std(InsertAfter_noseqcon_cp1_5)
InsertAfter_noseqcon_cp3_9_mean = np.mean(InsertAfter_noseqcon_cp3_9)
InsertAfter_noseqcon_cp3_9_std = np.std(InsertAfter_noseqcon_cp3_9)
InsertAfter_noseqcon_cp1_9_mean = np.mean(InsertAfter_noseqcon_cp1_9)
InsertAfter_noseqcon_cp1_9_std = np.std(InsertAfter_noseqcon_cp1_9)

InsertAfter_nolambda_cp3_5_mean = np.mean(InsertAfter_nolambda_cp3_5)
InsertAfter_nolambda_cp3_5_std = np.std(InsertAfter_nolambda_cp3_5)
InsertAfter_nolambda_cp1_5_mean = np.mean(InsertAfter_nolambda_cp1_5)
InsertAfter_nolambda_cp1_5_std = np.std(InsertAfter_nolambda_cp1_5)
InsertAfter_nolambda_cp3_9_mean = np.mean(InsertAfter_nolambda_cp3_9)
InsertAfter_nolambda_cp3_9_std = np.std(InsertAfter_nolambda_cp3_9)
InsertAfter_nolambda_cp1_9_mean = np.mean(InsertAfter_nolambda_cp1_9)
InsertAfter_nolambda_cp1_9_std = np.std(InsertAfter_nolambda_cp1_9)

InsertBefore_cp3_5 = np.array(allinfo_InsertBefore[tests[0]])
InsertBefore_cp1_5 = np.array(allinfo_InsertBefore[tests[1]])
InsertBefore_cp3_9 = np.array(allinfo_InsertBefore[tests[2]])
InsertBefore_cp1_9 = np.array(allinfo_InsertBefore[tests[3]])
InsertBefore_noseqcon_cp3_5 = np.array(allinfo_InsertBefore[tests[4]])
InsertBefore_noseqcon_cp1_5 = np.array(allinfo_InsertBefore[tests[5]])
InsertBefore_noseqcon_cp3_9 = np.array(allinfo_InsertBefore[tests[6]])
InsertBefore_noseqcon_cp1_9 = np.array(allinfo_InsertBefore[tests[7]])
InsertBefore_nolambda_cp3_5 = np.array(allinfo_InsertBefore[tests[8]])
InsertBefore_nolambda_cp1_5 = np.array(allinfo_InsertBefore[tests[9]])
InsertBefore_nolambda_cp3_9 = np.array(allinfo_InsertBefore[tests[10]])
InsertBefore_nolambda_cp1_9 = np.array(allinfo_InsertBefore[tests[11]])

InsertBefore_cp3_5_mean = np.mean(InsertBefore_cp3_5)
InsertBefore_cp3_5_std = np.std(InsertBefore_cp3_5)
InsertBefore_cp1_5_mean = np.mean(InsertBefore_cp1_5)
InsertBefore_cp1_5_std = np.std(InsertBefore_cp1_5)
InsertBefore_cp3_9_mean = np.mean(InsertBefore_cp3_9)
InsertBefore_cp3_9_std = np.std(InsertBefore_cp3_9)
InsertBefore_cp1_9_mean = np.mean(InsertBefore_cp1_9)
InsertBefore_cp1_9_std = np.std(InsertBefore_cp1_9)

InsertBefore_noseqcon_cp3_5_mean = np.mean(InsertBefore_noseqcon_cp3_5)
InsertBefore_noseqcon_cp3_5_std = np.std(InsertBefore_noseqcon_cp3_5)
InsertBefore_noseqcon_cp1_5_mean = np.mean(InsertBefore_noseqcon_cp1_5)
InsertBefore_noseqcon_cp1_5_std = np.std(InsertBefore_noseqcon_cp1_5)
InsertBefore_noseqcon_cp3_9_mean = np.mean(InsertBefore_noseqcon_cp3_9)
InsertBefore_noseqcon_cp3_9_std = np.std(InsertBefore_noseqcon_cp3_9)
InsertBefore_noseqcon_cp1_9_mean = np.mean(InsertBefore_noseqcon_cp1_9)
InsertBefore_noseqcon_cp1_9_std = np.std(InsertBefore_noseqcon_cp1_9)

InsertBefore_nolambda_cp3_5_mean = np.mean(InsertBefore_nolambda_cp3_5)
InsertBefore_nolambda_cp3_5_std = np.std(InsertBefore_nolambda_cp3_5)
InsertBefore_nolambda_cp1_5_mean = np.mean(InsertBefore_nolambda_cp1_5)
InsertBefore_nolambda_cp1_5_std = np.std(InsertBefore_nolambda_cp1_5)
InsertBefore_nolambda_cp3_9_mean = np.mean(InsertBefore_nolambda_cp3_9)
InsertBefore_nolambda_cp3_9_std = np.std(InsertBefore_nolambda_cp3_9)
InsertBefore_nolambda_cp1_9_mean = np.mean(InsertBefore_nolambda_cp1_9)
InsertBefore_nolambda_cp1_9_std = np.std(InsertBefore_nolambda_cp1_9)


orig_cp3_mean = (Expand_cp3_5_mean, Expand_cp3_9_mean, Remove_cp3_5_mean, Remove_cp3_9_mean, InsertAfter_cp3_5_mean, InsertAfter_cp3_9_mean, InsertBefore_cp3_5_mean, InsertBefore_cp3_9_mean)
orig_cp1_mean = (Expand_cp1_5_mean, Expand_cp1_9_mean, Remove_cp1_5_mean, Remove_cp1_9_mean, InsertAfter_cp1_5_mean, InsertAfter_cp1_9_mean, InsertBefore_cp1_5_mean, InsertBefore_cp1_9_mean)
noseqcon_cp3_mean = (Expand_noseqcon_cp3_5_mean, Expand_noseqcon_cp3_9_mean, Remove_noseqcon_cp3_5_mean, Remove_noseqcon_cp3_9_mean, InsertAfter_noseqcon_cp3_5_mean, InsertAfter_noseqcon_cp3_9_mean, InsertBefore_noseqcon_cp3_5_mean, InsertBefore_noseqcon_cp3_9_mean)
noseqcon_cp1_mean = (Expand_noseqcon_cp1_5_mean, Expand_noseqcon_cp1_9_mean, Remove_noseqcon_cp1_5_mean, Remove_noseqcon_cp1_9_mean, InsertAfter_noseqcon_cp1_5_mean, InsertAfter_noseqcon_cp1_9_mean, InsertBefore_noseqcon_cp1_5_mean, InsertBefore_noseqcon_cp1_9_mean)
nolambda_cp3_mean = (Expand_nolambda_cp3_5_mean, Expand_nolambda_cp3_9_mean, Remove_nolambda_cp3_5_mean, Remove_nolambda_cp3_9_mean, InsertAfter_nolambda_cp3_5_mean, InsertAfter_nolambda_cp3_9_mean, InsertBefore_nolambda_cp3_5_mean, InsertBefore_nolambda_cp3_9_mean)
nolambda_cp1_mean = (Expand_nolambda_cp1_5_mean, Expand_nolambda_cp1_9_mean, Remove_nolambda_cp1_5_mean, Remove_nolambda_cp1_9_mean, InsertAfter_nolambda_cp1_5_mean, InsertAfter_nolambda_cp1_9_mean, InsertBefore_nolambda_cp1_5_mean, InsertBefore_nolambda_cp1_9_mean)

orig_cp3_std = (Expand_cp3_5_std, Expand_cp3_9_std, Remove_cp3_5_std, Remove_cp3_9_std, InsertAfter_cp3_5_std, InsertAfter_cp3_9_std, InsertBefore_cp3_5_std, InsertBefore_cp3_9_std)
orig_cp1_std = (Expand_cp1_5_std, Expand_cp1_9_std, Remove_cp1_5_std, Remove_cp1_9_std, InsertAfter_cp1_5_std, InsertAfter_cp1_9_std, InsertBefore_cp1_5_std, InsertBefore_cp1_9_std)
noseqcon_cp3_std = (Expand_noseqcon_cp3_5_std, Expand_noseqcon_cp3_9_std, Remove_noseqcon_cp3_5_std, Remove_noseqcon_cp3_9_std, InsertAfter_noseqcon_cp3_5_std, InsertAfter_noseqcon_cp3_9_std, InsertBefore_noseqcon_cp3_5_std, InsertBefore_noseqcon_cp3_9_std)
noseqcon_cp1_std = (Expand_noseqcon_cp1_5_std, Expand_noseqcon_cp1_9_std, Remove_noseqcon_cp1_5_std, Remove_noseqcon_cp1_9_std, InsertAfter_noseqcon_cp1_5_std, InsertAfter_noseqcon_cp1_9_std, InsertBefore_noseqcon_cp1_5_std, InsertBefore_noseqcon_cp1_9_std)
nolambda_cp3_std = (Expand_nolambda_cp3_5_std, Expand_nolambda_cp3_9_std, Remove_nolambda_cp3_5_std, Remove_nolambda_cp3_9_std, InsertAfter_nolambda_cp3_5_std, InsertAfter_nolambda_cp3_9_std, InsertBefore_nolambda_cp3_5_std, InsertBefore_nolambda_cp3_9_std)
nolambda_cp1_std = (Expand_nolambda_cp1_5_std, Expand_nolambda_cp1_9_std, Remove_nolambda_cp1_5_std, Remove_nolambda_cp1_9_std, InsertAfter_nolambda_cp1_5_std, InsertAfter_nolambda_cp1_9_std, InsertBefore_nolambda_cp1_5_std, InsertBefore_nolambda_cp1_9_std)

ind = np.arange(len(orig_cp3_std))  # the x locations for the groups
width = 0.5  # the width of the bars

fig, ax = plt.subplots()
rects2 = ax.bar(ind - width/2, orig_cp1_mean, width/6, yerr=orig_cp1_std,
                label='Original-CS1', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
rects4 = ax.bar(ind - width/3, noseqcon_cp1_mean, width/6, yerr=noseqcon_cp1_std,
                label='noSeqConcat-CS1', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
rects6 = ax.bar(ind - width/6, nolambda_cp1_mean, width/6, yerr=nolambda_cp1_std,
                label='noLambda-CS1', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
rects1 = ax.bar(ind + width/6, orig_cp3_mean, width/6, yerr=orig_cp3_std,
                label='Original-CS3', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
rects3 = ax.bar(ind + width/3, noseqcon_cp3_mean, width/6, yerr=noseqcon_cp3_std,
                label='noSeqConcat-CS3', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
rects5 = ax.bar(ind + width/2, nolambda_cp3_mean, width/6, yerr=nolambda_cp3_std,
                label='noLambda-CS3', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))

# Add some text for labels, title and custom x-axis tick labels, etc.
ax.set_ylabel('Execution time (second)')
ax.set_xticks(ind)
ax.set_xticklabels(('Expand (4.8.5)', 'Expand (4.8.9)', 'Remove (4.8.5)', 'Remove (4.8.9)', 'InsertAfter (4.8.5)', 'InsertAfter (4.8.9)', 'InsertBefore (4.8.5)', 'InsertBefore (4.8.9)'), fontsize=13)
ax.legend()


def autolabel(rects, xpos='center'):
    """
    Attach a text label above each bar in *rects*, displaying its height.

    *xpos* indicates which side to place the text w.r.t. the center of
    the bar. It can be one of the following {'center', 'right', 'left'}.
    """

    ha = {'center': 'center', 'right': 'left', 'left': 'right'}
    offset = {'center': 0, 'right': 1, 'left': -1}

    for rect in rects:
        height = rect.get_height()
        if height == 100:
            ax.annotate('{}'.format("T"),
                        xy=(rect.get_x() + rect.get_width() / 2, height),
                        xytext=(offset[xpos]*3, 3),  # use 3 points offset
                        textcoords="offset points",  # in both directions
                        ha=ha[xpos], va='bottom')


autolabel(rects1)
autolabel(rects2)
autolabel(rects3)
autolabel(rects4)
autolabel(rects5)
autolabel(rects6)

fig.tight_layout()

plt.yscale("log")
plt.show()