#!/bin/bash
python3 new_test.py trio testcases/io_new >> log/98trio_io_t.txt
python3 new_test.py trio testcases/ref_new >> log/98trio_ref_t.txt

python3 log_to_csv.py log/98trio_io_t.txt 98trio_io_t
python3 log_to_csv.py log/98trio_ref_t.txt 98trio_ref_t

# python3 log_to_csv.py log/trio_io_log.txt io_log.csv
# python3 log_to_csv.py log/burst_io_log.txt io_log.csv
# python3 log_to_csv.py log/smyth_io_log.txt io_log.csv

# python3 log_to_csv.py log/trio_ref_log.txt ref_log.csv
# python3 log_to_csv.py log/burst_ref_log.txt ref_log.csv
# python3 log_to_csv.py log/smyth_ref_log.txt ref_log.csv

# python3 log_to_csv.py log/trio_refex_log.txt refex_log.csv
# python3 log_to_csv.py log/burst_refex_log.txt refex_log.csv
# python3 log_to_csv.py log/smyth_refex_log.txt refex_log.csv