import os
import sys
import time
import subprocess
import platform
import argparse

path = os.getcwd() + "/"
gnu_time = "gtime"
if platform.system() == "Linux":
    gnu_time = "/usr/bin/time"

def make_correct():
    ref = path + "benchmarks/ref"
    os.makedirs(path + "result/correct", exist_ok=True)
    for file in os.listdir(ref):
        with open(ref+"/"+file, 'r') as f:
            data = f.read().split("equiv")
            if(len(data) == 2):
                sol = data[1].strip()
                s = open(path + "result/correct/" + file + ".out", 'w')
                s.write(sol)
            else: print("invalid ref benchmark error (" + file + ")")

def run_solver(timeout=120, benchmark="io", ablation=False):
    if ablation:
        solvers = ["trio", "trio_T", "trio_L", "trio_--"]
        prefix = path + "result/ablation_"+benchmark+"_result"
        with open(path + "ablation_list", "r") as f: 
            lists = f.readlines()
    else:
        solvers = ["trio", "burst", "smyth"]
        prefix = path + "result/"+benchmark+"_result"
        with open(path + "bench_list", "r") as f: 
            lists = f.readlines()
    timeout = str(timeout)
    os.makedirs(prefix, exist_ok=True)
    # with open(path + "bench_list", "r") as f: lists = f.readlines()
    for solver in solvers:
        for fname in lists:
            file = fname.strip()
            file_locate = path + "benchmarks/" + benchmark + "/" + file
            solfilename = prefix + "/" + file + "." + solver + ".sol"
            csvfilename = prefix + "/" + file + "." + solver + ".csv"
            if solver == "trio":
                cmd = gnu_time + " -f 'Time(s): %e \nMem(Kb): %M' timeout " + timeout +" burst/BurstCmdLine.exe -print-data -use-trio " + file_locate
            elif solver == "burst":
                cmd = gnu_time + " -f 'Time(s): %e \nMem(Kb): %M' timeout " + timeout +" burst/BurstCmdLine.exe -print-data " + file_locate
            elif solver == "smyth":
                cmd = gnu_time + " -f 'Time(s): %e \nMem(Kb): %M' timeout " + timeout +" burst/BurstCmdLine.exe -print-data -use-smyth " + file_locate
            elif solver == "trio_T":
                cmd = gnu_time + " -f 'Time(s): %e \nMem(Kb): %M' timeout " + timeout +" burst/BurstCmdLine.exe -print-data -use-trio -trio_options \"-noinvmap\" " + file_locate
            elif solver == "trio_L":
                cmd = gnu_time + " -f 'Time(s): %e \nMem(Kb): %M' timeout " + timeout +" burst/BurstCmdLine.exe -print-data -use-trio -trio_options \"-nofilter\" " + file_locate
            elif solver == "trio_--":
                cmd = gnu_time + " -f 'Time(s): %e \nMem(Kb): %M' timeout " + timeout +" burst/BurstCmdLine.exe -print-data -use-trio -trio_options \"-noinvmap -nofilter\" " + file_locate
            # print("cmd : " + cmd)
            proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)
            sol = ""
            # size, iter, time, mem
            csv_data =""
            if (proc.returncode == 0):
                (s, temp) = proc.stdout.split("Size: ")
                (size, iter) = temp.split("Iter: ")
                (err, tm) = proc.stderr.split("Time(s): ")
                (time, mem) = tm.split("Mem(Kb): ")
                sol = s.strip()
                csv_data += (size.strip() + "," + iter.strip() + "," + time.strip() + "," + mem.strip())
            else:
                (err, mem) = proc.stderr.split("Mem(Kb): ")
                csv_data += ("N/A,N/A," + timeout +"," + mem.strip())
            with open(solfilename, "w") as sol_file:
                sol_file.write(sol)
            with open(csvfilename, "w") as csv_file:
                csv_file.write(csv_data)

def check_equal(correctSol, solverSol, IOFile):
    cmd = "burst/BurstCmdLine.exe -check-equiv1 " + correctSol + " -check-equiv2 " + solverSol + " " + IOFile
    proc = subprocess.run(cmd, capture_output=True, text=True, shell=True)
    if proc.returncode == 0:
        return "correct"
    else:
        return "incorrect"

def make_csv(benchmark="io"):
    # testname / trio_time / size / correct / burst_time / size / correct / smyth_time / size / correct
    if benchmark == "io":
        csv_string = "Test,Trio_Time,Trio_Size,Trio_Correct,Burst_Time,Burst_Size,Burst_Correct,Smyth_Time,Smyth_Size,Smyth_Correct\n"
    elif benchmark == "ref":
        csv_string = "Test,Trio_Time,Trio_Size,Trio_Iter,Burst_Time,Burst_Size,Burst_Iter,Smyth_Time,Smyth_Size,Smyth_Iter\n"
    else: print("fail to make csv"); return -1
    with open(path + "bench_list", "r") as f: lists = f.readlines()
    prefix = path + "result/"+benchmark+"_result"
    solvers = ["trio", "burst", "smyth"]
    for filename in lists:
        # del .mls
        fname = filename.strip()
        file = fname[:-4]
        for solver in solvers:
            solfilename = prefix + "/" + fname + "." + solver + ".sol"
            csvfilename = prefix + "/" + fname + "." + solver + ".csv"
            # correctfile = path + "result/correct/" + fname + ".out"
            # correctdata = check_equal(correctfile, solfilename, path + "benchmarks/" + benchmark + "/" + fname)
            try:
                with open(csvfilename, 'r') as csvfile:
                    szie_data, iter_data, time_data, mem_data = csvfile.read().split(",")
                    csv_string += (file + "," + time_data + "," + szie_data + ",")
                    if (benchmark == "io"):
                        correctfile = path + "result/correct/" + fname + ".out"
                        correctdata = check_equal(correctfile, solfilename, path + "benchmarks/" + benchmark + "/" + fname)
                        csv_string += correctdata
                    elif (benchmark == "ref"):
                        csv_string += iter_data
                    else: 
                        print("fail to make csv")
                        return -1
                    if (solver != "smyth"):
                        csv_string += ","
            except FileNotFoundError:
                print("Not found result file. please run first")
                exit()
        csv_string += "\n"
    print(csv_string)
    with open(path + "result/"+benchmark+"_result.csv", "w") as csv_file: csv_file.write(csv_string)

def tester():
    with open(path + "bench_list", "r") as f: lists = f.readlines()
    for fname in lists:
        file = fname.strip()[:-4]
        print(file)

def parse_args():
    parser = argparse.ArgumentParser()

    parser.add_argument('--print_result', type=int, default=0, help="print result (1: IO, 2: Ref, 3: Ablation")

    subparsers = parser.add_subparsers(dest="cmd")
    subparser = subparsers.add_parser("io", help="Run IO benchmarks")
    subparser.add_argument("--timeout", type=int, default=120)

    subparser = subparsers.add_parser("ref", help="Run Ref benchmarks")
    subparser.add_argument("--timeout", type=int, default=120)

    subparser = subparsers.add_parser("ablation", help="Run Ablation Study")
    subparser.add_argument("--timeout", type=int, default=120)
    return parser.parse_args()


def main():
    # file ="list_fold.mls"
    # check_equal(path + "/result/correct/"+file+".out",path + "/result/io_result/"+file+".smyth.sol", path + "/benchmarks/io/"+file+"")
    # exit()
    make_csv("ref")
    exit()
    args = parse_args()
    if args.print_result == 1:
        make_correct()
        print("io")
    elif args.print_result == 2:
        print("ref")
    elif args.print_result == 3:
        print("ablation")
    else:
        if args.cmd in ["io", "ref"]:
            run_solver(args.timeout, args.cmd, False)
        elif args.cmd == "ablation":
            run_solver(args.timeout, "io", True)
            run_solver(args.timeout, "ref", True)
        else:
            print("invalid command")
if __name__ == "__main__":
    main()