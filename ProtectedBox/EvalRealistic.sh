EXEC=".stack-work/dist/x86_64-linux-nopie/Cabal-1.24.2.0/build/protected-box-app/protected-box-app"
FMT="%e, %U, %M"

if [ $1 = "tarball" ]
then
  $EXEC "tarball-prepare" $2 $3
fi

echo "Evaluating \`$1\` for 1..$2"

echo "TINI time (S), TINI user time (S), TINI memory (KB)"
cp /dev/null "ExperimentData/tini$1.csv"
for N in `seq 1 $2`
do
  /usr/bin/time -f "$FMT" $EXEC "+RTS" -N8 "-RTS" $1 $N "$3" "tini" 2>&1 | tee -a "ExperimentData/tini$1.csv"
done

echo "SME time (S), SME user time (S), SME memory (KB)"
cp /dev/null "ExperimentData/sme$1.csv"
for N in `seq 1 $2`
do
  /usr/bin/time -f "$FMT" $EXEC "+RTS" -N8 "-RTS" $1 $N "$3" "sme" 2>&1 | tee -a "ExperimentData/sme$1.csv"
done

echo "FSME time (S), FSME user time (S), FSME memory (KB)"
cp /dev/null "ExperimentData/fsme$1.csv"
for N in `seq 1 $2`
do
  /usr/bin/time -f "$FMT" $EXEC "+RTS" -N8 "-RTS" $1 $N "$3" "fsme" 2>&1 | tee -a "ExperimentData/fsme$1.csv"
done

echo "UNF time (S), UNF user time (S), UNF memory (KB)"
cp /dev/null "ExperimentData/unf$1.csv"
for N in `seq 1 $2`
do
  /usr/bin/time -f "$FMT" $EXEC "+RTS" -N8 "-RTS" $1 $N "$3" "unf" 2>&1 | tee -a "ExperimentData/unf$1.csv"
done
