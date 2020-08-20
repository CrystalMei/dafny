#!/usr/bin/env python3

import os
import glob
import re
import sys
import math

# use cases and their directory names
tests = [
  "CP3-4.8.5", "CP1-4.8.5", "CP3-4.8.9", "CP1-4.8.9", 
  "ADT-CP3-4.8.5", "ADT-CP1-4.8.5", "ADT-CP3-4.8.9", "ADT-CP1-4.8.9",
  "CP3-4.8.8", "CP1-4.8.8", "ADT-CP3-4.8.8", "ADT-CP1-4.8.8"
]

loc_orig_5 = os.path.join('Logs_DLL_8.20', 'Logs_orig_4.8.5', '*.trace')
loc_orig_9 = os.path.join('Logs_DLL_8.20', 'Logs_orig_4.8.9', '*.trace')
loc_adt_5 = os.path.join('Logs_DLL_8.20', 'Logs_adt_4.8.5', '*.trace')
loc_adt_9 = os.path.join('Logs_DLL_8.20', 'Logs_adt_4.8.9', '*.trace')
loc_orig_8 = os.path.join('Logs_DLL_8.20', 'Logs_orig_4.8.8', '*.trace')
loc_adt_8 = os.path.join('Logs_DLL_8.20', 'Logs_adt_4.8.8', '*.trace')
file_orig_5 = glob.glob(loc_orig_5)
file_orig_9 = glob.glob(loc_orig_9)
file_adt_5 = glob.glob(loc_adt_5)
file_adt_9 = glob.glob(loc_adt_9)
file_orig_8 = glob.glob(loc_orig_8)
file_adt_8 = glob.glob(loc_adt_8)
# print(file_orig_5)

allinfo1 = {}
allinfo2 = {}
allinfo3 = {}

def get_time (files, index):
    for f in files:
        outfile = open(f, 'r')
        data = outfile.readlines()
        outfile.close()
        for i in range(0, len(data)):
            if 'Verifying Impl$$_module.__default.SMN__Correct ...' in data[i]:
                time = re.findall("\[([0-9.]*) s, ([0-9.]*) proof obligations\]  ([a-z]+)", data[i + 1])
                if len(time) > 0:
                    if time[0][2] == "verified":
                        if 'CP3' in f:
                            allinfo1[tests[index]] = allinfo1.get(tests[index], [])
                            allinfo1[tests[index]] += [float(time[0][0])]
                        else:
                            allinfo1[tests[index+1]] = allinfo1.get(tests[index+1], [])
                            allinfo1[tests[index+1]] += [float(time[0][0])]
                    else:
                        if time[0][2] == "timed":
                            if 'CP3' in f:
                                allinfo1[tests[index]] = allinfo1.get(tests[index], [])
                                allinfo1[tests[index]] += [float(100)]
                            else:
                                allinfo1[tests[index+1]] = allinfo1.get(tests[index+1], [])
                                allinfo1[tests[index+1]] += [float(100)]
                        else:
                            allinfo1[tests[index]] = allinfo1.get(tests[index], [])
                            allinfo1[tests[index+1]] = allinfo1.get(tests[index+1], [])
            
            if 'Verifying Impl$$_module.__default.SMN_k__Correct ...' in data[i]:
                time = re.findall("\[([0-9.]*) s, ([0-9.]*) proof obligations\]  ([a-z]+)", data[i + 1])
                if len(time) > 0:
                    if time[0][2] == "verified":
                        if 'CP3' in f:
                            allinfo2[tests[index]] = allinfo2.get(tests[index], [])
                            allinfo2[tests[index]] += [float(time[0][0])]
                        else:
                            allinfo2[tests[index+1]] = allinfo2.get(tests[index+1], [])
                            allinfo2[tests[index+1]] += [float(time[0][0])] 
                    else:
                        if time[0][2] == "timed":
                            if 'CP3' in f:
                                allinfo2[tests[index]] = allinfo2.get(tests[index], [])
                                allinfo2[tests[index]] += [float(100)]
                            else:
                                allinfo2[tests[index+1]] = allinfo2.get(tests[index+1], [])
                                allinfo2[tests[index+1]] += [float(100)]
                        else:
                            allinfo2[tests[index]] = allinfo2.get(tests[index], [])
                            allinfo2[tests[index+1]] = allinfo2.get(tests[index+1], [])

            if 'Verifying Impl$$_module.__default.SMN_k_k__Correct ...' in data[i]:
                time = re.findall("\[([0-9.]*) s, ([0-9.]*) proof obligations\]  ([a-z]+)", data[i + 1])
                if len(time) > 0:
                    if time[0][2] == "verified":
                        if 'CP3' in f:
                            allinfo3[tests[index]] = allinfo3.get(tests[index], [])
                            allinfo3[tests[index]] += [float(time[0][0])]
                        else:
                            allinfo3[tests[index+1]] = allinfo3.get(tests[index+1], [])
                            allinfo3[tests[index+1]] += [float(time[0][0])]
                    else:
                        if time[0][2] == "timed":
                            if 'CP3' in f:
                                allinfo3[tests[index]] = allinfo3.get(tests[index], [])
                                allinfo3[tests[index]] += [float(100)]
                            else:
                                allinfo3[tests[index+1]] = allinfo3.get(tests[index+1], [])
                                allinfo3[tests[index+1]] += [float(100)]
                        else:
                            allinfo3[tests[index]] = allinfo3.get(tests[index], [])
                            allinfo3[tests[index+1]] = allinfo3.get(tests[index+1], [])

get_time(file_orig_5, 0)
get_time(file_orig_9, 2)
get_time(file_adt_5, 4)
get_time(file_adt_9, 6)
get_time(file_orig_8, 8)
get_time(file_adt_8, 10)

# print(allinfo1)
# print(allinfo2)
# print(allinfo3)

# print a CSV
def show_csv(allinfo, info):
  for test in tests:
    if test in allinfo:
        times = allinfo[test]
        print(test + ", " + info),
        for i in times:
            print(", " + str(i)),
        print ("\n"),

# show_csv(allinfo1, "SMN_Correct")
# show_csv(allinfo2, "SMN'_Correct")
# show_csv(allinfo3, "SMN''_Correct")

import numpy as np
import matplotlib
import matplotlib.pyplot as plt
matplotlib.rcParams.update({'font.size': 16})

SMN1_cp3_5 = np.array(allinfo1.get(tests[0], []))
SMN1_cp1_5 = np.array(allinfo1.get(tests[1], []))
SMN1_cp3_9 = np.array(allinfo1.get(tests[2], []))
SMN1_cp1_9 = np.array(allinfo1.get(tests[3], []))
SMN1_adt_cp3_5 = np.array(allinfo1.get(tests[4], []))
SMN1_adt_cp1_5 = np.array(allinfo1.get(tests[5], []))
SMN1_adt_cp3_9 = np.array(allinfo1.get(tests[6], []))
SMN1_adt_cp1_9 = np.array(allinfo1.get(tests[7], []))

SMN1_cp3_5_mean = np.mean(SMN1_cp3_5)
SMN1_cp3_5_std = np.std(SMN1_cp3_5)
SMN1_cp1_5_mean = np.mean(SMN1_cp1_5)
SMN1_cp1_5_std = np.std(SMN1_cp1_5)
SMN1_cp3_9_mean = np.mean(SMN1_cp3_9)
SMN1_cp3_9_std = np.std(SMN1_cp3_9)
SMN1_cp1_9_mean = np.mean(SMN1_cp1_9)
SMN1_cp1_9_std = np.std(SMN1_cp1_9)

SMN1_adt_cp3_5_mean = np.mean(SMN1_adt_cp3_5)
SMN1_adt_cp3_5_std = np.std(SMN1_adt_cp3_5)
SMN1_adt_cp1_5_mean = np.mean(SMN1_adt_cp1_5)
SMN1_adt_cp1_5_std = np.std(SMN1_adt_cp1_5)
SMN1_adt_cp3_9_mean = np.mean(SMN1_adt_cp3_9)
SMN1_adt_cp3_9_std = np.std(SMN1_adt_cp3_9)
SMN1_adt_cp1_9_mean = np.mean(SMN1_adt_cp1_9)
SMN1_adt_cp1_9_std = np.std(SMN1_adt_cp1_9)

# SMN1_cp3_8 = np.array(allinfo1[tests[8]])
# SMN1_cp1_8 = np.array(allinfo1[tests[9]])
# SMN1_adt_cp3_8 = np.array(allinfo1[tests[10]])
# SMN1_adt_cp1_8 = np.array(allinfo1[tests[11]])
# SMN1_cp3_8_mean = np.mean(SMN1_cp3_8)
# SMN1_cp3_8_std = np.std(SMN1_cp3_8)
# SMN1_cp1_8_mean = np.mean(SMN1_cp1_8)
# SMN1_cp1_8_std = np.std(SMN1_cp1_8)
# SMN1_adt_cp3_8_mean = np.mean(SMN1_adt_cp3_8)
# SMN1_adt_cp3_8_std = np.std(SMN1_adt_cp3_8)
# SMN1_adt_cp1_8_mean = np.mean(SMN1_adt_cp1_8)
# SMN1_adt_cp1_8_std = np.std(SMN1_adt_cp1_8)

SMN2_cp3_5 = np.array(allinfo2.get(tests[0], []))
SMN2_cp1_5 = np.array(allinfo2.get(tests[1], []))
SMN2_cp3_9 = np.array(allinfo2.get(tests[2], []))
SMN2_cp1_9 = np.array(allinfo2.get(tests[3], []))
SMN2_adt_cp3_5 = np.array(allinfo2.get(tests[4], []))
SMN2_adt_cp1_5 = np.array(allinfo2.get(tests[5], []))
SMN2_adt_cp3_9 = np.array(allinfo2.get(tests[6], []))
SMN2_adt_cp1_9 = np.array(allinfo2.get(tests[7], []))

SMN2_cp3_5_mean = np.mean(SMN2_cp3_5)
SMN2_cp3_5_std = np.std(SMN2_cp3_5)
SMN2_cp1_5_mean = np.mean(SMN2_cp1_5)
SMN2_cp1_5_std = np.std(SMN2_cp1_5)
SMN2_cp3_9_mean = np.mean(SMN2_cp3_9)
SMN2_cp3_9_std = np.std(SMN2_cp3_9)
SMN2_cp1_9_mean = np.mean(SMN2_cp1_9)
SMN2_cp1_9_std = np.std(SMN2_cp1_9)

SMN2_adt_cp3_5_mean = np.mean(SMN2_adt_cp3_5)
SMN2_adt_cp3_5_std = np.std(SMN2_adt_cp3_5)
SMN2_adt_cp1_5_mean = np.mean(SMN2_adt_cp1_5)
SMN2_adt_cp1_5_std = np.std(SMN2_adt_cp1_5)
SMN2_adt_cp3_9_mean = np.mean(SMN2_adt_cp3_9)
SMN2_adt_cp3_9_std = np.std(SMN2_adt_cp3_9)
SMN2_adt_cp1_9_mean = np.mean(SMN2_adt_cp1_9)
SMN2_adt_cp1_9_std = np.std(SMN2_adt_cp1_9)

# SMN2_cp3_8 = np.array(allinfo2[tests[8]])
# SMN2_cp1_8 = np.array(allinfo2[tests[9]])
# SMN2_adt_cp3_8 = np.array(allinfo2[tests[10]])
# SMN2_adt_cp1_8 = np.array(allinfo2[tests[11]])
# SMN2_cp3_8_mean = np.mean(SMN2_cp3_8)
# SMN2_cp3_8_std = np.std(SMN2_cp3_8)
# SMN2_cp1_8_mean = np.mean(SMN2_cp1_8)
# SMN2_cp1_8_std = np.std(SMN2_cp1_8)
# SMN2_adt_cp3_8_mean = np.mean(SMN2_adt_cp3_8)
# SMN2_adt_cp3_8_std = np.std(SMN2_adt_cp3_8)
# SMN2_adt_cp1_8_mean = np.mean(SMN2_adt_cp1_8)
# SMN2_adt_cp1_8_std = np.std(SMN2_adt_cp1_8)

SMN3_cp3_5 = np.array(allinfo3.get(tests[0], []))
SMN3_cp1_5 = np.array(allinfo3.get(tests[1], []))
SMN3_cp3_9 = np.array(allinfo3.get(tests[2], []))
SMN3_cp1_9 = np.array(allinfo3.get(tests[3], []))
SMN3_adt_cp3_5 = np.array(allinfo3.get(tests[4], []))
SMN3_adt_cp1_5 = np.array(allinfo3.get(tests[5], []))
SMN3_adt_cp3_9 = np.array(allinfo3.get(tests[6], []))
SMN3_adt_cp1_9 = np.array(allinfo3.get(tests[7], []))

SMN3_cp3_5_mean = np.mean(SMN3_cp3_5)
SMN3_cp3_5_std = np.std(SMN3_cp3_5)
SMN3_cp1_5_mean = np.mean(SMN3_cp1_5)
SMN3_cp1_5_std = np.std(SMN3_cp1_5)
SMN3_cp3_9_mean = np.mean(SMN3_cp3_9)
SMN3_cp3_9_std = np.std(SMN3_cp3_9)
SMN3_cp1_9_mean = np.mean(SMN3_cp1_9)
SMN3_cp1_9_std = np.std(SMN3_cp1_9)

SMN3_adt_cp3_5_mean = np.mean(SMN3_adt_cp3_5)
SMN3_adt_cp3_5_std = np.std(SMN3_adt_cp3_5)
SMN3_adt_cp1_5_mean = np.mean(SMN3_adt_cp1_5)
SMN3_adt_cp1_5_std = np.std(SMN3_adt_cp1_5)
SMN3_adt_cp3_9_mean = np.mean(SMN3_adt_cp3_9)
SMN3_adt_cp3_9_std = np.std(SMN3_adt_cp3_9)
SMN3_adt_cp1_9_mean = np.mean(SMN3_adt_cp1_9)
SMN3_adt_cp1_9_std = np.std(SMN3_adt_cp1_9)

# SMN3_cp3_8 = np.array(allinfo3[tests[8]])
# SMN3_cp1_8 = np.array(allinfo3[tests[9]])
# SMN3_adt_cp3_8 = np.array(allinfo3[tests[10]])
# SMN3_adt_cp1_8 = np.array(allinfo3[tests[11]])
# SMN3_cp3_8_mean = np.mean(SMN3_cp3_8)
# SMN3_cp3_8_std = np.std(SMN3_cp3_8)
# SMN3_cp1_8_mean = np.mean(SMN3_cp1_8)
# SMN3_cp1_8_std = np.std(SMN3_cp1_8)
# SMN3_adt_cp3_8_mean = np.mean(SMN3_adt_cp3_8)
# SMN3_adt_cp3_8_std = np.std(SMN3_adt_cp3_8)
# SMN3_adt_cp1_8_mean = np.mean(SMN3_adt_cp1_8)
# SMN3_adt_cp1_8_std = np.std(SMN3_adt_cp1_8)

# orig_cp3_mean = (SMN1_cp3_5_mean, SMN1_cp3_8_mean, SMN1_cp3_9_mean, SMN2_cp3_5_mean, SMN2_cp3_8_mean, SMN2_cp3_9_mean, SMN3_cp3_5_mean, SMN3_cp3_8_mean, SMN3_cp3_9_mean)
# orig_cp1_mean = (SMN1_cp1_5_mean, SMN1_cp1_8_mean, SMN1_cp1_9_mean, SMN2_cp1_5_mean, SMN2_cp1_8_mean, SMN2_cp1_9_mean, SMN3_cp1_5_mean, SMN3_cp1_8_mean, SMN3_cp1_9_mean)
# adt_cp3_mean = (SMN1_adt_cp3_5_mean, SMN1_adt_cp3_8_mean, SMN1_adt_cp3_9_mean, SMN2_adt_cp3_5_mean, SMN2_adt_cp3_8_mean, SMN2_adt_cp3_9_mean, SMN3_adt_cp3_5_mean, SMN3_adt_cp3_8_mean, SMN3_adt_cp3_9_mean)
# adt_cp1_mean = (SMN1_adt_cp1_5_mean, SMN1_adt_cp1_8_mean, SMN1_adt_cp1_9_mean, SMN2_adt_cp1_5_mean, SMN2_adt_cp1_8_mean, SMN2_adt_cp1_9_mean, SMN3_adt_cp1_5_mean, SMN3_adt_cp1_8_mean, SMN3_adt_cp1_9_mean)

# orig_cp3_std = (SMN1_cp3_5_std, SMN1_cp3_8_std, SMN1_cp3_9_std, SMN2_cp3_5_std, SMN2_cp3_8_std, SMN2_cp3_9_std, SMN3_cp3_5_std, SMN3_cp3_8_std, SMN3_cp3_9_std)
# orig_cp1_std = (SMN1_cp1_5_std, SMN1_cp1_8_std, SMN1_cp1_9_std, SMN2_cp1_5_std, SMN2_cp1_8_std, SMN2_cp1_9_std, SMN3_cp1_5_std, SMN3_cp1_8_std, SMN3_cp1_9_std)
# adt_cp3_std = (SMN1_adt_cp3_5_std, SMN1_adt_cp3_8_std, SMN1_adt_cp3_9_std, SMN2_adt_cp3_5_std, SMN2_adt_cp3_8_std, SMN2_adt_cp3_9_std, SMN3_adt_cp3_5_std, SMN3_adt_cp3_8_std, SMN3_adt_cp3_9_std)
# adt_cp1_std = (SMN1_adt_cp1_5_std, SMN1_adt_cp1_8_std, SMN1_adt_cp1_9_std, SMN2_adt_cp1_5_std, SMN2_adt_cp1_8_std, SMN2_adt_cp1_9_std, SMN3_adt_cp1_5_std, SMN3_adt_cp1_8_std, SMN3_adt_cp1_9_std)


orig_cp3_mean = (SMN1_cp3_5_mean, SMN1_cp3_9_mean, SMN2_cp3_5_mean, SMN2_cp3_9_mean, SMN3_cp3_5_mean, SMN3_cp3_9_mean)
orig_cp1_mean = (SMN1_cp1_5_mean, SMN1_cp1_9_mean, SMN2_cp1_5_mean, SMN2_cp1_9_mean, SMN3_cp1_5_mean, SMN3_cp1_9_mean)
adt_cp3_mean = (SMN1_adt_cp3_5_mean, SMN1_adt_cp3_9_mean, SMN2_adt_cp3_5_mean, SMN2_adt_cp3_9_mean, SMN3_adt_cp3_5_mean, SMN3_adt_cp3_9_mean)
adt_cp1_mean = (SMN1_adt_cp1_5_mean, SMN1_adt_cp1_9_mean, SMN2_adt_cp1_5_mean, SMN2_adt_cp1_9_mean, SMN3_adt_cp1_5_mean, SMN3_adt_cp1_9_mean)

orig_cp3_std = (SMN1_cp3_5_std, SMN1_cp3_9_std, SMN2_cp3_5_std, SMN2_cp3_9_std, SMN3_cp3_5_std, SMN3_cp3_9_std)
orig_cp1_std = (SMN1_cp1_5_std, SMN1_cp1_9_std, SMN2_cp1_5_std, SMN2_cp1_9_std, SMN3_cp1_5_std, SMN3_cp1_9_std)
adt_cp3_std = (SMN1_adt_cp3_5_std, SMN1_adt_cp3_9_std, SMN2_adt_cp3_5_std, SMN2_adt_cp3_9_std, SMN3_adt_cp3_5_std, SMN3_adt_cp3_9_std)
adt_cp1_std = (SMN1_adt_cp1_5_std, SMN1_adt_cp1_9_std, SMN2_adt_cp1_5_std, SMN2_adt_cp1_9_std, SMN3_adt_cp1_5_std, SMN3_adt_cp1_9_std)

ind = np.arange(len(orig_cp3_std))  # the x locations for the groups
width = 0.5  # the width of the bars

fig, ax = plt.subplots()
rects2 = ax.bar(ind - width/2, orig_cp1_mean, width/4, yerr=orig_cp1_std,
                label='Original-CS1', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
rects4 = ax.bar(ind - width/4, adt_cp1_mean, width/4, yerr=adt_cp1_std,
                label='ADT-CS1', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
rects1 = ax.bar(ind + width/4, orig_cp3_mean, width/4, yerr=orig_cp3_std,
                label='Original-CS3', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))
rects3 = ax.bar(ind + width/2, adt_cp3_mean, width/4, yerr=adt_cp3_std,
                label='ADT-CS3', error_kw=dict(ecolor='black', lw=1, capsize=3, capthick=1))

# Add some text for labels, title and custom x-axis tick labels, etc.
ax.set_ylabel('Execution time (second)')
ax.set_xticks(ind)
# ax.set_xticklabels(('SMN_Correct (4.8.5)', 'SMN_Correct (4.8.8)', 'SMN_Correct (4.8.9)', "SMN'_Correct (4.8.5)", "SMN'_Correct (4.8.8)", "SMN'_Correct (4.8.9)", "SMN''_Correct (4.8.5)", "SMN''_Correct (4.8.8)", "SMN''_Correct (4.8.9)"), fontsize=10)
ax.set_xticklabels(('SMN_Correct (4.8.5)', 'SMN_Correct (4.8.9)', "SMN'_Correct (4.8.5)", "SMN'_Correct (4.8.9)", "SMN''_Correct (4.8.5)", "SMN''_Correct (4.8.9)"), fontsize=14)
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
        ax.annotate('{}'.format(height),
                    xy=(rect.get_x() + rect.get_width() / 2, height),
                    xytext=(offset[xpos]*3, 3),  # use 3 points offset
                    textcoords="offset points",  # in both directions
                    ha=ha[xpos], va='bottom')


# autolabel(rects1, "left")
# autolabel(rects2, "right")

fig.tight_layout()

plt.show()