import os
import sys
import subprocess
import platform
from telnetlib import theNULL

# args[1] : synthesizer
# args[2] : file

# gtime -f 'Time(s): %e \nMem(Kb): %M' timeout 10 burst/BurstCmdLine.exe -print-data -use-trio benchmarks/io/expr.mls
args = sys.argv
file = args[2]
synth = args[1]
gnu_time = "gtime"
if platform.system() == "Linux":
    gnu_time = "/usr/bin/time"
print("synthesizer :" + synth)
if synth == "trio" :
    cmd = gnu_time + " -f 'Time(s): %e \nMem(Kb): %M' timeout 120 burst/BurstCmdLine.exe -print-data -use-trio " + file
    proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)

    print("prog : "+file)
    print(proc.stdout)
    print(proc.stderr)

elif synth == "burst" :
    cmd = gnu_time + " -f 'Time(s): %e \nMem(Kb): %M' timeout 120 burst/BurstCmdLine.exe -print-data " + file
    proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)

    print("prog : "+file)
    print(proc.stdout)
    print(proc.stderr)

elif synth == "smyth" :
    cmd = gnu_time + " -f 'Time(s): %e \nMem(Kb): %M' timeout 120 burst/BurstCmdLine.exe -print-data -use-smyth " + file
    proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)

    print("prog : "+file)
    print(proc.stdout)
    print(proc.stderr)

else : print("invalid synthesizer !")

# mac은 gtime (brew install gnu-time)
# cmd = "/usr/bin/time -l timeout 10m ./main.sh -max_height 6 -init_comp_size 5 " + args[1]
# cmd = "/usr/bin/time -l timeout 10m ./_build/default/bin/main.exe -max_height 6 -init_comp_size 5 " + args[1]
# cmd = "gtime -f 'time(s): %e \nmem(Kb): %M' timeout 10m ./_build/default/bin/main.exe -max_height 6 -init_comp_size 5 " + args[1]
# proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)

# print("prog : "+args[1])
# print(proc.stderr)
