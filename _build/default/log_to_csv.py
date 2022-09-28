import sys

# args[1] : log name
args = sys.argv
file = args[1]
outfile = args[2]

f = open(file)
# f.close()
s = "file,size,iter,time,mem\n"
data = f.readlines()
# print(data)
checker = False
out = open('log/csv/'+outfile+'.csv','a')
for line in data :
    # print(line)
    if "prog : " in line:
        s += (line.strip("prog : ").strip() + ",")
    if "Size: " in line:
        s += (line.strip("Size: ").strip() + ",")
        checker = True
    if "Iter: " in line:
        s += (line.strip("Iter: ").strip() + ",")
            
    if "Time(s): " in line:
        if checker :
            s += (line.strip("Time(s): ").strip() + ",")
            checker = False
        else :
            s += "0,0,"
            s += (line.strip("Time(s): ").strip() + ",")
    if "Mem(Kb): " in line:
        # print(s)
        s += (line.strip("Mem(Kb): ").strip() + "\n")
        # print(s)
        out.write(s)
        s = ""
f.close()
out.close()
