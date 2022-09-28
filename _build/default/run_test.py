import os
import sys
import subprocess
from telnetlib import theNULL

# args[1] : synthesizer
# args[2] : file
args = sys.argv
file = args[2]
synth = args[1]
to = 120
print("synthesizer :" + synth)
if synth == "trio" :
    cmd = "gtime -f 'Time(s): %e \nMem(Kb): %M' timeout 120 burst/BurstCmdLine.exe -print-data -use-trio " + file
    proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)

    print("prog : "+file)
    print(proc.stdout)
    print(proc.stderr)

elif synth == "burst" :
    cmd = "gtime -f 'Time(s): %e \nMem(Kb): %M' timeout 120 burst/BurstCmdLine.exe -print-data " + file
    proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)

    print("prog : "+file)
    print(proc.stdout)
    print(proc.stderr)

elif synth == "smyth" :
    cmd = "gtime -f 'Time(s): %e \nMem(Kb): %M' timeout 120 burst/BurstCmdLine.exe -print-data -use-smyth " + file
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
