#!/bin/sh
# Final-binary timings for representative rows (CPU seconds are the meaningful numbers on a shared machine).
cd "$(dirname "$0")"
for p in 733 743 797 1031 4507 839 1307 2819; do
  python3 driver.py $p > timing/final_$p.json 2>&1
done
V2_MINPOLY=1 python3 driver.py 359,1433 > timing/final_359_1433.json 2>&1
