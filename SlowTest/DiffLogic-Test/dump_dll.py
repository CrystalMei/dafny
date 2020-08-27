#!/usr/bin/env python3

import os
import glob
import re
import sys
import math

# use cases and their directory names
tests = [
  "CP3", "CP1", "SDL-CP3", "SDL-CP1", 
  "DDL-CP3", "DDL-CP1", "WDL-CP3", "WDL-CP1",
  "CP3-5", "CP1-5", "CP3-8", "CP1-8", "CP3-9", "CP1-9"
]

loc_orig = os.path.join('Logs_default', '*.trace')
loc_sdl = os.path.join('Logs_solver1', '*.trace')
loc_ddl = os.path.join('Logs_solver3', '*.trace')
loc_wdl = os.path.join('Logs_solver7', '*.trace')
loc_orig5 = os.path.join('Logs_default5', '*.trace')
loc_orig8 = os.path.join('Logs_default8', '*.trace')
loc_orig9 = os.path.join('Logs_default9', '*.trace')
file_orig = glob.glob(loc_orig)
file_sdl = glob.glob(loc_sdl)
file_ddl = glob.glob(loc_ddl)
file_wdl = glob.glob(loc_wdl)
file_orig5 = glob.glob(loc_orig5)
file_orig8 = glob.glob(loc_orig8)
file_orig9 = glob.glob(loc_orig9)

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
                                allinfo_Expand[tests[index]] += [float(100)]
                            else:
                                allinfo_Expand[tests[index+1]] = allinfo_Expand.get(tests[index+1], [])
                                allinfo_Expand[tests[index+1]] += [float(100)]
                        else:
                            allinfo_Expand[tests[index]] = allinfo_Expand.get(tests[index], [])
                            allinfo_Expand[tests[index+1]] = allinfo_Expand.get(tests[index+1], [])
            
            if 'Verifying Impl$$_module.__default.Test__Remove ...' in data[i]:
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
                                allinfo_Remove[tests[index]] += [float(100)]
                            else:
                                allinfo_Remove[tests[index+1]] = allinfo_Remove.get(tests[index+1], [])
                                allinfo_Remove[tests[index+1]] += [float(100)]
                        else:
                            allinfo_Remove[tests[index]] = allinfo_Remove.get(tests[index], [])
                            allinfo_Remove[tests[index+1]] = allinfo_Remove.get(tests[index+1], [])

            if 'Verifying Impl$$_module.__default.Test__InsertAfter ...' in data[i]:
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
                                allinfo_InsertAfter[tests[index]] += [float(100)]
                            else:
                                allinfo_InsertAfter[tests[index+1]] = allinfo_InsertAfter.get(tests[index+1], [])
                                allinfo_InsertAfter[tests[index+1]] += [float(100)]
                        else:
                            allinfo_InsertAfter[tests[index]] = allinfo_InsertAfter.get(tests[index], [])
                            allinfo_InsertAfter[tests[index+1]] = allinfo_InsertAfter.get(tests[index+1], [])

            if 'Verifying Impl$$_module.__default.Test__InsertBefore ...' in data[i]:
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
                                allinfo_InsertBefore[tests[index]] += [float(100)]
                            else:
                                allinfo_InsertBefore[tests[index+1]] = allinfo_InsertBefore.get(tests[index+1], [])
                                allinfo_InsertBefore[tests[index+1]] += [float(100)]
                        else:
                            allinfo_InsertBefore[tests[index]] = allinfo_InsertBefore.get(tests[index], [])
                            allinfo_InsertBefore[tests[index+1]] = allinfo_InsertBefore.get(tests[index+1], [])

get_time(file_orig, 0)
get_time(file_sdl, 2)
get_time(file_ddl, 4)
get_time(file_wdl, 6)
get_time(file_orig5, 8)
get_time(file_orig8, 10)
get_time(file_orig9, 12)

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
matplotlib.rcParams.update({'font.size': 16})

Expand_cp3 = np.array(allinfo_Expand[tests[0]])
Expand_cp1 = np.array(allinfo_Expand[tests[1]])
Expand_cp3_sdl = np.array(allinfo_Expand[tests[2]])
Expand_cp1_sdl = np.array(allinfo_Expand[tests[3]])
Expand_cp3_ddl = np.array(allinfo_Expand[tests[4]])
Expand_cp1_ddl = np.array(allinfo_Expand[tests[5]])
Expand_cp3_wdl = np.array(allinfo_Expand[tests[6]])
Expand_cp1_wdl = np.array(allinfo_Expand[tests[7]])
Expand_cp3_5 = np.array(allinfo_Expand[tests[8]])
Expand_cp1_5 = np.array(allinfo_Expand[tests[9]])

Expand_cp3_mean = np.mean(Expand_cp3)
Expand_cp3_std = np.std(Expand_cp3)
Expand_cp1_mean = np.mean(Expand_cp1)
Expand_cp1_std = np.std(Expand_cp1)
Expand_cp3_sdl_mean = np.mean(Expand_cp3_sdl)
Expand_cp3_sdl_std = np.std(Expand_cp3_sdl)
Expand_cp1_sdl_mean = np.mean(Expand_cp1_sdl)
Expand_cp1_sdl_std = np.std(Expand_cp1_sdl)
Expand_cp3_ddl_mean = np.mean(Expand_cp3_ddl)
Expand_cp3_ddl_std = np.std(Expand_cp3_ddl)
Expand_cp1_ddl_mean = np.mean(Expand_cp1_ddl)
Expand_cp1_ddl_std = np.std(Expand_cp1_ddl)
Expand_cp3_wdl_mean = np.mean(Expand_cp3_wdl)
Expand_cp3_wdl_std = np.std(Expand_cp3_wdl)
Expand_cp1_wdl_mean = np.mean(Expand_cp1_wdl)
Expand_cp1_wdl_std = np.std(Expand_cp1_wdl)
Expand_cp3_5_mean = np.mean(Expand_cp3_5)
Expand_cp3_5_std = np.std(Expand_cp3_5)
Expand_cp1_5_mean = np.mean(Expand_cp1_5)
Expand_cp1_5_std = np.std(Expand_cp1_5)

# Expand_cp3_8 = np.array(allinfo_Expand[tests[10]])
# Expand_cp1_8 = np.array(allinfo_Expand[tests[11]])
# Expand_cp3_9 = np.array(allinfo_Expand[tests[12]])
# Expand_cp1_9 = np.array(allinfo_Expand[tests[13]])
# Expand_cp3_8_mean = np.mean(Expand_cp3_8)
# Expand_cp3_8_std = np.std(Expand_cp3_8)
# Expand_cp1_8_mean = np.mean(Expand_cp1_8)
# Expand_cp1_8_std = np.std(Expand_cp1_8)
# Expand_cp3_9_mean = np.mean(Expand_cp3_9)
# Expand_cp3_9_std = np.std(Expand_cp3_9)
# Expand_cp1_9_mean = np.mean(Expand_cp1_9)
# Expand_cp1_9_std = np.std(Expand_cp1_9)


Remove_cp3 = np.array(allinfo_Remove[tests[0]])
Remove_cp1 = np.array(allinfo_Remove[tests[1]])
Remove_cp3_sdl = np.array(allinfo_Remove[tests[2]])
Remove_cp1_sdl = np.array(allinfo_Remove[tests[3]])
Remove_cp3_ddl = np.array(allinfo_Remove[tests[4]])
Remove_cp1_ddl = np.array(allinfo_Remove[tests[5]])
Remove_cp3_wdl = np.array(allinfo_Remove[tests[6]])
Remove_cp1_wdl = np.array(allinfo_Remove[tests[7]])
Remove_cp3_5 = np.array(allinfo_Remove[tests[8]])
Remove_cp1_5 = np.array(allinfo_Remove[tests[9]])

Remove_cp3_mean = np.mean(Remove_cp3)
Remove_cp3_std = np.std(Remove_cp3)
Remove_cp1_mean = np.mean(Remove_cp1)
Remove_cp1_std = np.std(Remove_cp1)
Remove_cp3_sdl_mean = np.mean(Remove_cp3_sdl)
Remove_cp3_sdl_std = np.std(Remove_cp3_sdl)
Remove_cp1_sdl_mean = np.mean(Remove_cp1_sdl)
Remove_cp1_sdl_std = np.std(Remove_cp1_sdl)
Remove_cp3_ddl_mean = np.mean(Remove_cp3_ddl)
Remove_cp3_ddl_std = np.std(Remove_cp3_ddl)
Remove_cp1_ddl_mean = np.mean(Remove_cp1_ddl)
Remove_cp1_ddl_std = np.std(Remove_cp1_ddl)
Remove_cp3_wdl_mean = np.mean(Remove_cp3_wdl)
Remove_cp3_wdl_std = np.std(Remove_cp3_wdl)
Remove_cp1_wdl_mean = np.mean(Remove_cp1_wdl)
Remove_cp1_wdl_std = np.std(Remove_cp1_wdl)
Remove_cp3_5_mean = np.mean(Remove_cp3_5)
Remove_cp3_5_std = np.std(Remove_cp3_5)
Remove_cp1_5_mean = np.mean(Remove_cp1_5)
Remove_cp1_5_std = np.std(Remove_cp1_5)

# Remove_cp3_8 = np.array(allinfo_Remove[tests[10]])
# Remove_cp1_8 = np.array(allinfo_Remove[tests[11]])
# Remove_cp3_9 = np.array(allinfo_Remove[tests[12]])
# Remove_cp1_9 = np.array(allinfo_Remove[tests[13]])
# Remove_cp3_8_mean = np.mean(Remove_cp3_8)
# Remove_cp3_8_std = np.std(Remove_cp3_8)
# Remove_cp1_8_mean = np.mean(Remove_cp1_8)
# Remove_cp1_8_std = np.std(Remove_cp1_8)
# Remove_cp3_9_mean = np.mean(Remove_cp3_9)
# Remove_cp3_9_std = np.std(Remove_cp3_9)
# Remove_cp1_9_mean = np.mean(Remove_cp1_9)
# Remove_cp1_9_std = np.std(Remove_cp1_9)

InsertAfter_cp3 = np.array(allinfo_InsertAfter[tests[0]])
InsertAfter_cp1 = np.array(allinfo_InsertAfter[tests[1]])
InsertAfter_cp3_sdl = np.array(allinfo_InsertAfter[tests[2]])
InsertAfter_cp1_sdl = np.array(allinfo_InsertAfter[tests[3]])
InsertAfter_cp3_ddl = np.array(allinfo_InsertAfter[tests[4]])
InsertAfter_cp1_ddl = np.array(allinfo_InsertAfter[tests[5]])
InsertAfter_cp3_wdl = np.array(allinfo_InsertAfter[tests[6]])
InsertAfter_cp1_wdl = np.array(allinfo_InsertAfter[tests[7]])
InsertAfter_cp3_5 = np.array(allinfo_InsertAfter[tests[8]])
InsertAfter_cp1_5 = np.array(allinfo_InsertAfter[tests[9]])

InsertAfter_cp3_mean = np.mean(InsertAfter_cp3)
InsertAfter_cp3_std = np.std(InsertAfter_cp3)
InsertAfter_cp1_mean = np.mean(InsertAfter_cp1)
InsertAfter_cp1_std = np.std(InsertAfter_cp1)
InsertAfter_cp3_sdl_mean = np.mean(InsertAfter_cp3_sdl)
InsertAfter_cp3_sdl_std = np.std(InsertAfter_cp3_sdl)
InsertAfter_cp1_sdl_mean = np.mean(InsertAfter_cp1_sdl)
InsertAfter_cp1_sdl_std = np.std(InsertAfter_cp1_sdl)
InsertAfter_cp3_ddl_mean = np.mean(InsertAfter_cp3_ddl)
InsertAfter_cp3_ddl_std = np.std(InsertAfter_cp3_ddl)
InsertAfter_cp1_ddl_mean = np.mean(InsertAfter_cp1_ddl)
InsertAfter_cp1_ddl_std = np.std(InsertAfter_cp1_ddl)
InsertAfter_cp3_wdl_mean = np.mean(InsertAfter_cp3_wdl)
InsertAfter_cp3_wdl_std = np.std(InsertAfter_cp3_wdl)
InsertAfter_cp1_wdl_mean = np.mean(InsertAfter_cp1_wdl)
InsertAfter_cp1_wdl_std = np.std(InsertAfter_cp1_wdl)
InsertAfter_cp3_5_mean = np.mean(InsertAfter_cp3_5)
InsertAfter_cp3_5_std = np.std(InsertAfter_cp3_5)
InsertAfter_cp1_5_mean = np.mean(InsertAfter_cp1_5)
InsertAfter_cp1_5_std = np.std(InsertAfter_cp1_5)

# InsertAfter_cp3_8 = np.array(allinfo_InsertAfter[tests[10]])
# InsertAfter_cp1_8 = np.array(allinfo_InsertAfter[tests[11]])
# InsertAfter_cp3_9 = np.array(allinfo_InsertAfter[tests[12]])
# InsertAfter_cp1_9 = np.array(allinfo_InsertAfter[tests[13]])
# InsertAfter_cp3_8_mean = np.mean(InsertAfter_cp3_8)
# InsertAfter_cp3_8_std = np.std(InsertAfter_cp3_8)
# InsertAfter_cp1_8_mean = np.mean(InsertAfter_cp1_8)
# InsertAfter_cp1_8_std = np.std(InsertAfter_cp1_8)
# InsertAfter_cp3_9_mean = np.mean(InsertAfter_cp3_9)
# InsertAfter_cp3_9_std = np.std(InsertAfter_cp3_9)
# InsertAfter_cp1_9_mean = np.mean(InsertAfter_cp1_9)
# InsertAfter_cp1_9_std = np.std(InsertAfter_cp1_9)


InsertBefore_cp3 = np.array(allinfo_InsertBefore[tests[0]])
InsertBefore_cp1 = np.array(allinfo_InsertBefore[tests[1]])
InsertBefore_cp3_sdl = np.array(allinfo_InsertBefore[tests[2]])
InsertBefore_cp1_sdl = np.array(allinfo_InsertBefore[tests[3]])
InsertBefore_cp3_ddl = np.array(allinfo_InsertBefore[tests[4]])
InsertBefore_cp1_ddl = np.array(allinfo_InsertBefore[tests[5]])
InsertBefore_cp3_wdl = np.array(allinfo_InsertBefore[tests[6]])
InsertBefore_cp1_wdl = np.array(allinfo_InsertBefore[tests[7]])
InsertBefore_cp3_5 = np.array(allinfo_InsertBefore[tests[8]])
InsertBefore_cp1_5 = np.array(allinfo_InsertBefore[tests[9]])

InsertBefore_cp3_mean = np.mean(InsertBefore_cp3)
InsertBefore_cp3_std = np.std(InsertBefore_cp3)
InsertBefore_cp1_mean = np.mean(InsertBefore_cp1)
InsertBefore_cp1_std = np.std(InsertBefore_cp1)
InsertBefore_cp3_sdl_mean = np.mean(InsertBefore_cp3_sdl)
InsertBefore_cp3_sdl_std = np.std(InsertBefore_cp3_sdl)
InsertBefore_cp1_sdl_mean = np.mean(InsertBefore_cp1_sdl)
InsertBefore_cp1_sdl_std = np.std(InsertBefore_cp1_sdl)
InsertBefore_cp3_ddl_mean = np.mean(InsertBefore_cp3_ddl)
InsertBefore_cp3_ddl_std = np.std(InsertBefore_cp3_ddl)
InsertBefore_cp1_ddl_mean = np.mean(InsertBefore_cp1_ddl)
InsertBefore_cp1_ddl_std = np.std(InsertBefore_cp1_ddl)
InsertBefore_cp3_wdl_mean = np.mean(InsertBefore_cp3_wdl)
InsertBefore_cp3_wdl_std = np.std(InsertBefore_cp3_wdl)
InsertBefore_cp1_wdl_mean = np.mean(InsertBefore_cp1_wdl)
InsertBefore_cp1_wdl_std = np.std(InsertBefore_cp1_wdl)
InsertBefore_cp3_5_mean = np.mean(InsertBefore_cp3_5)
InsertBefore_cp3_5_std = np.std(InsertBefore_cp3_5)
InsertBefore_cp1_5_mean = np.mean(InsertBefore_cp1_5)
InsertBefore_cp1_5_std = np.std(InsertBefore_cp1_5)

# InsertBefore_cp3_8 = np.array(allinfo_InsertBefore[tests[10]])
# InsertBefore_cp1_8 = np.array(allinfo_InsertBefore[tests[11]])
# InsertBefore_cp3_9 = np.array(allinfo_InsertBefore[tests[12]])
# InsertBefore_cp1_9 = np.array(allinfo_InsertBefore[tests[13]])
# InsertBefore_cp3_8_mean = np.mean(InsertBefore_cp3_8)
# InsertBefore_cp3_8_std = np.std(InsertBefore_cp3_8)
# InsertBefore_cp1_8_mean = np.mean(InsertBefore_cp1_8)
# InsertBefore_cp1_8_std = np.std(InsertBefore_cp1_8)
# InsertBefore_cp3_9_mean = np.mean(InsertBefore_cp3_9)
# InsertBefore_cp3_9_std = np.std(InsertBefore_cp3_9)
# InsertBefore_cp1_9_mean = np.mean(InsertBefore_cp1_9)
# InsertBefore_cp1_9_std = np.std(InsertBefore_cp1_9)


orig_cp3_mean = (Expand_cp3_mean, Remove_cp3_mean, InsertAfter_cp3_mean, InsertBefore_cp3_mean)
orig_cp1_mean = (Expand_cp1_mean, Remove_cp1_mean, InsertAfter_cp1_mean, InsertBefore_cp1_mean)
sdl_cp3_mean = (Expand_cp3_sdl_mean, Remove_cp3_sdl_mean, InsertAfter_cp3_sdl_mean, InsertBefore_cp3_sdl_mean)
sdl_cp1_mean = (Expand_cp1_sdl_mean, Remove_cp1_sdl_mean, InsertAfter_cp1_sdl_mean, InsertBefore_cp1_sdl_mean)
ddl_cp3_mean = (Expand_cp3_ddl_mean, Remove_cp3_ddl_mean, InsertAfter_cp3_ddl_mean, InsertBefore_cp3_ddl_mean)
ddl_cp1_mean = (Expand_cp1_ddl_mean, Remove_cp1_ddl_mean, InsertAfter_cp1_ddl_mean, InsertBefore_cp1_ddl_mean)
wdl_cp3_mean = (Expand_cp3_wdl_mean, Remove_cp3_wdl_mean, InsertAfter_cp3_wdl_mean, InsertBefore_cp3_wdl_mean)
wdl_cp1_mean = (Expand_cp1_wdl_mean, Remove_cp1_wdl_mean, InsertAfter_cp1_wdl_mean, InsertBefore_cp1_wdl_mean)
orig_cp3_5_mean = (Expand_cp3_5_mean, Remove_cp3_5_mean, InsertAfter_cp3_5_mean, InsertBefore_cp3_5_mean)
orig_cp1_5_mean = (Expand_cp1_5_mean, Remove_cp1_5_mean, InsertAfter_cp1_5_mean, InsertBefore_cp1_5_mean)
# orig_cp3_8_mean = (Expand_cp3_8_mean, Remove_cp3_8_mean, InsertAfter_cp3_8_mean, InsertBefore_cp3_8_mean)
# orig_cp1_8_mean = (Expand_cp1_8_mean, Remove_cp1_8_mean, InsertAfter_cp1_8_mean, InsertBefore_cp1_8_mean)
# orig_cp3_9_mean = (Expand_cp3_9_mean, Remove_cp3_9_mean, InsertAfter_cp3_9_mean, InsertBefore_cp3_9_mean)
# orig_cp1_9_mean = (Expand_cp1_9_mean, Remove_cp1_9_mean, InsertAfter_cp1_9_mean, InsertBefore_cp1_9_mean)

orig_cp3_std = (Expand_cp3_std, Remove_cp3_std, InsertAfter_cp3_std, InsertBefore_cp3_std)
orig_cp1_std = (Expand_cp1_std, Remove_cp1_std, InsertAfter_cp1_std, InsertBefore_cp1_std)
sdl_cp3_std = (Expand_cp3_sdl_std, Remove_cp3_sdl_std, InsertAfter_cp3_sdl_std, InsertBefore_cp3_sdl_std)
sdl_cp1_std = (Expand_cp1_sdl_std, Remove_cp1_sdl_std, InsertAfter_cp1_sdl_std, InsertBefore_cp1_sdl_std)
ddl_cp3_std = (Expand_cp3_ddl_std, Remove_cp3_ddl_std, InsertAfter_cp3_ddl_std, InsertBefore_cp3_ddl_std)
ddl_cp1_std = (Expand_cp1_ddl_std, Remove_cp1_ddl_std, InsertAfter_cp1_ddl_std, InsertBefore_cp1_ddl_std)
wdl_cp3_std = (Expand_cp3_wdl_std, Remove_cp3_wdl_std, InsertAfter_cp3_wdl_std, InsertBefore_cp3_wdl_std)
wdl_cp1_std = (Expand_cp1_wdl_std, Remove_cp1_wdl_std, InsertAfter_cp1_wdl_std, InsertBefore_cp1_wdl_std)
orig_cp3_5_std = (Expand_cp3_5_std, Remove_cp3_5_std, InsertAfter_cp3_5_std, InsertBefore_cp3_5_std)
orig_cp1_5_std = (Expand_cp1_5_std, Remove_cp1_5_std, InsertAfter_cp1_5_std, InsertBefore_cp1_5_std)
# orig_cp3_8_std = (Expand_cp3_8_std, Remove_cp3_8_std, InsertAfter_cp3_8_std, InsertBefore_cp3_8_std)
# orig_cp1_8_std = (Expand_cp1_8_std, Remove_cp1_8_std, InsertAfter_cp1_8_std, InsertBefore_cp1_8_std)
# orig_cp3_9_std = (Expand_cp3_9_std, Remove_cp3_9_std, InsertAfter_cp3_9_std, InsertBefore_cp3_9_std)
# orig_cp1_9_std = (Expand_cp1_9_std, Remove_cp1_9_std, InsertAfter_cp1_9_std, InsertBefore_cp1_9_std)

ind = np.arange(len(orig_cp3_std))  # the x locations for the groups
width = 0.5  # the width of the bars

fig, ax = plt.subplots()
rects12 = ax.bar(ind - 5*width/8, orig_cp1_5_mean, width/8, yerr=orig_cp1_5_std,
                # label='Default-4.8.5-CS1', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=2))
                label='Default-4.8.5-CS1', color='dodgerblue', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=2))
rects1 = ax.bar(ind - 4*width/8, orig_cp1_mean, width/8, yerr=orig_cp1_std,
                # label='Default-CS1', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=2))
                label='Default-CS1', color='limegreen', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=2))
rects2 = ax.bar(ind - 3*width/8, sdl_cp1_mean, width/8, yerr=sdl_cp1_std,
                # label='SDL-CS1', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
                label='SDL-CS1', color='orange', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
rects3 = ax.bar(ind - 2*width/8, ddl_cp1_mean, width/8, yerr=ddl_cp1_std,
                # label='DDL-CS1', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
                label='DDL-CS1', color='hotpink', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
rects4 = ax.bar(ind - 1*width/8, wdl_cp1_mean, width/8, yerr=wdl_cp1_std,
                # label='WDL-CS1', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
                label='WDL-CS1', color='lightcoral', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))

rects51 = ax.bar(ind + 1*width/8, orig_cp3_5_mean, width/8, yerr=orig_cp3_5_std,
                # label='Default-4.8.5-CS3', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
                label='Default-4.8.5-CS3', color='darkblue', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
rects5 = ax.bar(ind + 2*width/8, orig_cp3_mean, width/8, yerr=orig_cp3_std,
                # label='Default-CS3', error_kw=dict(ecolor='black', lw=2, capsize=3, capthick=1))
                label='Default-CS3', color='darkgreen', error_kw=dict(ecolor='black', lw=2, capsize=3, capthick=1))
rects6 = ax.bar(ind + 3*width/8, sdl_cp3_mean, width/8, yerr=sdl_cp3_std,
                # label='SDL-CS3', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
                label='SDL-CS3', color='chocolate', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
rects7 = ax.bar(ind + 4*width/8, ddl_cp3_mean, width/8, yerr=ddl_cp3_std,
                # label='DDL-CS3', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
                label='DDL-CS3', color='purple', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
rects8 = ax.bar(ind + 5*width/8, wdl_cp3_mean, width/8, yerr=wdl_cp3_std,
                # label='WDL-CS3', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
                label='WDL-CS3', color='darkred', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))

# rects13 = ax.bar(ind - width/4, orig_cp1_8_mean, width/8, yerr=orig_cp1_8_std,
#                 label='Default-4.8.8-CS1', color='hotpink', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=2))
# rects14 = ax.bar(ind - 5*width/8, orig_cp1_9_mean, width/8, yerr=orig_cp1_9_std,
#                 label='Default-4.8.9-CS1', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=2))
                # label='Default-4.8.9-CS1', color='orange', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=2))
# rects52 = ax.bar(ind + 3 * width/8, orig_cp3_8_mean, width/8, yerr=orig_cp3_8_std,
#                 label='Default-4.8.8-CS3', color='purple', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
# rects53 = ax.bar(ind + width/4, orig_cp3_9_mean, width/8, yerr=orig_cp3_9_std,
#                 label='Default-4.8.9-CS3', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
                # label='Default-4.8.9-CS3', color='chocolate', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))

# Add some text for labels, title and custom x-axis tick labels, etc.
ax.set_ylabel('Execution time (second)', fontsize=20)
ax.set_xticks(ind)
ax.set_xticklabels(('Expand', 'Remove', 'InsertAfter', 'InsertBefore'), fontsize=20)
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
autolabel(rects12)
autolabel(rects2)
autolabel(rects3)
autolabel(rects4)
autolabel(rects5)
autolabel(rects51)
autolabel(rects6)
autolabel(rects7)
autolabel(rects8)

fig.tight_layout()

plt.yscale("log")
plt.show()