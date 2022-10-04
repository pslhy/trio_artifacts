import os
import sys
import time
import subprocess
import platform
import argparse
from unicodedata import category
import pretty_csv
import statistics
from tqdm import tqdm

path = os.getcwd() + "/"
gnu_time = "gtime"
if platform.system() == "Linux":
    gnu_time = "/usr/bin/time"

def mean_str(v):
    try:
        return '%7.1f' % statistics.mean(v)
    except:
        return 'N/A'

def sum_str(v):
    try:
        return '%7.1f' % sum(v)
    except:
        return 'N/A'

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
        print(solver + "synthesis...")
        for fname in tqdm(lists):
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
                cmd = gnu_time + " -f 'Time(s): %e \nMem(Kb): %M' timeout " + timeout +" burst/BurstCmdLine.exe -print-data -use-trio -trio-options \"-noinvmap\" " + file_locate
            elif solver == "trio_L":
                cmd = gnu_time + " -f 'Time(s): %e \nMem(Kb): %M' timeout " + timeout +" burst/BurstCmdLine.exe -print-data -use-trio -trio-options \"-nofilter\" " + file_locate
            elif solver == "trio_--":
                cmd = gnu_time + " -f 'Time(s): %e \nMem(Kb): %M' timeout " + timeout +" burst/BurstCmdLine.exe -print-data -use-trio -trio-options \"-noinvmap -nofilter\" " + file_locate
            # print("cmd : " + cmd)
            try:
                proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)
            except:
                proc = subprocess.run(cmd,stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
            sol = ""
            # size, iter, time, mem
            csv_data =""
            # stdout = proc.stdout.decode('utf-8')
            # proc.stdout = proc.stdout.replace("\r", "")
            if (proc.returncode == 0):
                (s, temp) = str(proc.stdout).split("Size: ")
                (size, iter) = temp.split("Iter: ")
                (err, tm) = str(proc.stderr).split("Time(s): ")
                (time, mem) = tm.split("Mem(Kb): ")
                sol = s.strip()
                csv_data += (size.strip() + "," + iter.strip() + "," + time.strip() + "," + mem.strip())
            else:
                (err, mem) = str(proc.stderr).split("Mem(Kb): ")
                csv_data += ("N/A,N/A," + timeout +"," + mem.strip())
            with open(solfilename, "w+") as sol_file:
                sol_file.write(sol)
            with open(csvfilename, "w+") as csv_file:
                csv_file.write(csv_data)

def check_equal(correctSol, solverSol, IOFile):
    cmd = "burst/BurstCmdLine.exe -check-equiv1 " + correctSol + " -check-equiv2 " + solverSol + " " + IOFile
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, shell=True)
    except:
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
    if proc.returncode == 0:
        return "correct"
    else:
        return "incorrect"

# for io and ref benchmarks
def make_csv(benchmark="io"):
    if benchmark == "io":
        csv_string = "Test,Trio_Time,Trio_Size,Trio_Correct,Burst_Time,Burst_Size,Burst_Correct,Smyth_Time,Smyth_Size,Smyth_Correct\n"
    elif benchmark == "ref":
        csv_string = "Test,Trio_Time,Trio_Size,Trio_Iter,Burst_Time,Burst_Size,Burst_Iter,Smyth_Time,Smyth_Size,Smyth_Iter\n"
    else: print("fail to make csv"); return -1
    with open(path + "bench_list", "r") as f: lists = f.readlines()
    prefix = path + "result/"+benchmark+"_result"
    solvers = ["trio", "burst", "smyth"]

    # save time data
    size_map = {}
    time_map = {}
    fastests = {}
    iter_map = {}
    for s in solvers:
        time_map[s] = []
        size_map[s] = []
        fastests[s] = 0
        iter_map[s] = []

    for filename in lists:
        # del .mls
        fname = filename.strip()
        csv_string += fname[:-4] + ","
        for solver in solvers:
            solfilename = prefix + "/" + fname + "." + solver + ".sol"
            csvfilename = prefix + "/" + fname + "." + solver + ".csv"
            try:
                with open(csvfilename, 'r') as csvfile:
                    size_data, iter_data, time_data, mem_data = csvfile.read().split(",")
                    # print(size_data.strip(), iter_data.strip(), time_data.strip(), mem_data.strip())
                    time_map[solver].append(float(time_data))
                    if float(time_data) >= 120:
                        # time_data = "timeout"
                        size_map[solver].append(-1)
                        iter_map[solver].append(-1)
                    else:
                        size_map[solver].append(int(size_data))
                        iter_map[solver].append(int(iter_data))
                    csv_string += (time_data + "," + size_data + ",")
                    if (benchmark == "io"):
                        if size_data == "N/A":
                            csv_string += "N/A"
                        else:
                            # !!!! correct Error... !!!!
                            correctfile = path + "result/correct/" + fname + ".out"
                            correctdata = check_equal(correctfile, solfilename, path + "benchmarks/" + benchmark + "/" + fname)
                            # correctdata = "correct"
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
    # print(csv_string)
    with open(path + "result/"+benchmark+"_result.csv", "w+") as csv_file: csv_file.write(csv_string)

    # compute fastest solver
    for i in range(0,len(time_map["trio"])):
        min_time = min([time_map[s][i] for s in solvers])
        if min_time == 120.0: continue
        # if same time, increase all
        if min_time == time_map["trio"][i]:
            fastests["trio"] += 1
        if min_time == time_map["burst"][i]:
            fastests["burst"] += 1
        if min_time == time_map["smyth"][i]:
            fastests["smyth"] += 1
    
    # remove timeout data
    for s in solvers:
        time_map[s] = [t for t in time_map[s] if t < 120]
        size_map[s] = [x for x in size_map[s] if x != -1]
        iter_map[s] = [x for x in iter_map[s] if x != -1]

    print("-" * 120)
    print("%8s %8s %8s %8s %8s" % (benchmark.upper(), "Total", "Trio", "Burst", "Smyth") )
    # correct ??? 
    print("%8s %8d %8d %8d %8d" % ("# Solved",
                                   len(lists),
                                   len([s for s in size_map["trio"] if s != -1]),
                                   len([s for s in size_map["burst"] if s != -1]),
                                   len([s for s in size_map["smyth"] if s != -1])))
    print("-" * 120)
    print("%8s %8s %8s %8s" % ("Data", "Trio", "Burst", "Smyth") )
    print("%8s %8d %8d %8d" % ("#Fastest", fastests["trio"], fastests["burst"], fastests["smyth"]))
    print("%8s %8s %8s %8s" % ("Avg_time", mean_str(time_map["trio"]), mean_str(time_map["burst"]), mean_str(time_map["smyth"])))
    if benchmark == "ref":
        print("%8s %8s %8s %8s" % ("Avg_iter", mean_str(iter_map["trio"]), mean_str(iter_map["burst"]), mean_str(iter_map["smyth"])))
    print("-" * 120)
 
def make_ablation_data():
    with open(path + "ablation_list", "r") as f: lists = f.readlines()
    solvers = ["trio", "trio_T", "trio_L", "trio_--"]
    categories = ["io", "ref"]
    time_map = {}
    size_map = {}

    for s in solvers:
        for c in categories:
            time_map[(s,c)] = []
            size_map[(s,c)] = []
            
    for filename in lists:
        # del .mls
        fname = filename.strip()
        for s in solvers:
            for c in categories:
                csvfilename = path + "result/ablation_" +c+ "_result/"+ fname + "." + s + ".csv"
                try:
                    with open(csvfilename, 'r') as csvfile:
                        size_data, iter_data, time_data, mem_data = csvfile.read().split(",")
                        time_map[(s,c)].append(float(time_data))
                        if float(time_data) >= 120:
                            size_map[(s,c)].append(-1)
                        else:
                            size_map[(s,c)].append(int(size_data))
                except FileNotFoundError:
                    print("Not found result file. please run first")
                    exit()
    # remove timeout data
    for s in solvers:
        for c in categories:
            time_map[(s,c)] = [t for t in time_map[(s,c)] if t < 120]
            size_map[(s,c)] = [x for x in size_map[(s,c)] if x != -1]
    
    # print result
    print("# Solved")
    print("-" * 120)
    print("%8s %8s %8s %8s %8s %8s" % ("", "Total", "Trio", "Trio_T", "Trio_L", "Trio_--") )
    for c in categories:
        print("%8s %8d %8d %8d %8d %8d" % (c,
                                            len(lists),
                                            len([s for s in size_map[("trio", c)] if s != -1 ]),
                                            len([s for s in size_map[("trio_T", c)] if s != -1 ]),
                                            len([s for s in size_map[("trio_L", c)] if s != -1 ]),
                                            len([s for s in size_map[("trio_--", c)] if s != -1 ])))
    print("-" * 120)
    print("Synthesis Time(s)" )
    print("-" * 120)
    print("%8s %8s %8s %8s %8s %8s" % ("", "","Trio", "Trio_T", "Trio_L", "Trio_--") )
    for c in categories:
        print("%8s %8s %8s %8s %8s %8s" % (c,"",
                                        sum_str(time_map[("trio", c)]),
                                        sum_str(time_map[("trio_T", c)]),
                                        sum_str(time_map[("trio_L", c)]),
                                        sum_str(time_map[("trio_--", c)])))
    print("-" * 120)
    
def make_pretty_csv(file):
    csv_file = path + "result/"+file
    new_file = path + "result/pretty_"+file
    if os.path.exists(new_file):
        os.remove(new_file)
    pretty_csv.pretty_file(csv_file, new_filename=new_file)
    with open(new_file, "r") as f: print(f.read())

# def tester():
#     cmd = "burst/BurstCmdLine.exe -print-data -use-trio -trio-options \"-nofilter\" " + "benchmarks/io/list_last2.mls"
#     try:
#         proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)
#     except:
#         proc = subprocess.run(cmd,stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
#     print(proc.stdout)
#     print(proc.stderr)

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
    args = parse_args()
    if args.print_result == 1:
        make_correct()
        make_csv("io")
        make_pretty_csv("io_result.csv")
    elif args.print_result == 2:
        make_csv("ref")
        make_pretty_csv("ref_result.csv")
    elif args.print_result == 3:
        make_ablation_data()
    else:
        if args.cmd in ["io", "ref"]:
            run_solver(args.timeout, args.cmd, False)
        elif args.cmd == "ablation":
            run_solver(args.timeout, "io", ablation=True)
            run_solver(args.timeout, "ref", ablation=True)
        else:
            print("invalid command")
if __name__ == "__main__":
    main()