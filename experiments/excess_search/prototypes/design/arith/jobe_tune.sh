cd /tmp/excess-bench/gf2x-1.3.0
make tune-lowlevel > tune-ll.log 2>&1
make tune-toom > tune-toom.log 2>&1
make tune-fft FFT_TUNING_LIMIT=2000000 > tune-fft.log 2>&1
make check > check2.log 2>&1
make install > inst.log 2>&1
echo done > TUNED
