#!/bin/bash
python3 new_test.py trio testcases/io_new >> log/99trio_io.txt
python3 new_test.py trio testcases/ref_new >> log/99trio_ref.txt

python3 log_to_csv.py log/99trio_io.txt 99trio_io
python3 log_to_csv.py log/99trio_ref.txt 99trio_ref

# python3 log_to_csv.py log/trio_io_log.txt io_log.csv
# python3 log_to_csv.py log/burst_io_log.txt io_log.csv
# python3 log_to_csv.py log/smyth_io_log.txt io_log.csv

# python3 log_to_csv.py log/trio_ref_log.txt ref_log.csv
# python3 log_to_csv.py log/burst_ref_log.txt ref_log.csv
# python3 log_to_csv.py log/smyth_ref_log.txt ref_log.csv

# python3 log_to_csv.py log/trio_refex_log.txt refex_log.csv
# python3 log_to_csv.py log/burst_refex_log.txt refex_log.csv
# python3 log_to_csv.py log/smyth_refex_log.txt refex_log.csv