EXEC=".stack-work/dist/x86_64-linux-nopie/Cabal-1.24.2.0/build/protected-box-app/protected-box-app"
FMT="%e, %U, %M"

for T in `seq 0 1000000 $2` 
do
  echo "With timeout $T: FSME time (S), FSME user time (S), FSME memory (KB)"
  cp /dev/null "ExperimentDataFSME/Data$T.csv"
  for N in `seq 1 $1`
  do
    /usr/bin/time -f "$FMT" $EXEC "+RTS" -N8 "-RTS" "hashes" $N "[$3, $T]" "fsme" 2>&1 | tee -a "ExperimentDataFSME/Data$T.csv"
  done
done
