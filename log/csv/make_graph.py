import matplotlib.pyplot as plt
import pandas as pd
import sys
# $1: typ
# $2 ~ $n csv files

# typ : io | ref
# data_name = [['EUSolver','CVC4','Euphony','Duet'],['^','D', 'X', 'o'],['g','r','m','b']]
data_name = [['$Trio^{T}$','$Trio^{L}$','$Trio^{--}$','$Trio$'],['^','v','D','o'],['g','m','r','b'],['none','none','none','none']]

typ = sys.argv[1]
datas = len(sys.argv) - 2

params = {'legend.fontsize': '18',
         'figure.figsize': (9, 6),
         'axes.labelsize': '20',
         'axes.titlesize':'30',
         'lines.linewidth' : '2',
         'xtick.labelsize':'17',
         'ytick.labelsize':'17'}

plt.rcParams.update(params)

# path1 = '/Users/hangyeol/Documents/project/test_compare/fta_'+typ+'_result.csv'
# path2 = '/Users/hangyeol/Documents/project/test_compare/eph_'+typ+'_result.csv'

for i in range(datas):
    globals()['path_{}'.format(i+1)] = str(sys.argv[i+2])

for i in range(datas):
    # df_1 ~ df_n
    globals()['df_{}'.format(i+1)] = pd.read_csv(globals()['path_{}'.format(i+1)])

# df_1 = pd.read_csv(path1)
# df_2 = pd.read_csv(path2)

# set label
# plt.title(typ.upper())
plt.title(typ+" Spec")
# plt.title("Input-Output Example")
plt.xlabel("# Solved (total = "+str(globals()['df_{}'.format(1)]['file'].count())+")")
plt.ylabel("Synthesis Time (s)")

# plt.xlim(30,60)
# plt.xlim(1,15)
plt.xticks(range(16), range(1,17))

# for i in range(datas):
#     print(globals()['df_{}'.format(i+1)])
# sort and cumulate
for i in range(datas):
    globals()['df_{}'.format(i+1)] = globals()['df_{}'.format(i+1)][globals()['df_{}'.format(i+1)]['time'].dropna() < 119.0].sort_values(by='time', ignore_index=True)

for i in range(datas):
    globals()['time_{}'.format(i+1)] = globals()['df_{}'.format(i+1)]['time'].cumsum()

# set data
for i in range(datas):
    plt.plot(globals()['time_{}'.format(i+1)], label=data_name[0][i]+' (solved = '+str(globals()['time_{}'.format(i+1)].count())+')', color=data_name[2][i], marker=data_name[1][i], markersize=10, markevery=2, fillstyle=data_name[3][i])

# print(globals()['time_{}'.format(4)])

plt.legend(loc='upper left')
# plt.show()
plt.savefig('./'+typ+'_graph_98.png')