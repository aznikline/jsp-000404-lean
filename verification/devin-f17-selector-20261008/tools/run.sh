#!/bin/bash
# usage: run.sh <tag> <cmd...> ; snapshots source bytes BEFORE run, logs raw output/exit/time
set -u
cd ~/work/sel; source ~/.elan/env
V=verification/devin-f17-selector-20261008/attempts
TAG=$1; shift
SRC=Jsp000404/DevinF17Selector.lean
cp $SRC $V/$TAG.source.lean
sha256sum $SRC > $V/$TAG.source.sha256
{ echo "cmd: $*"; echo "start: $(date -u +%FT%TZ)"; echo "host: $(hostname) $(nproc)cpu"; } > $V/$TAG.meta
/usr/bin/time -f "wall %e s, maxrss %M KB" -o $V/$TAG.time timeout 1800 "$@" > $V/$TAG.out 2>&1
ec=$?
{ echo "exit: $ec"; echo "end: $(date -u +%FT%TZ)"; } >> $V/$TAG.meta
cat $V/$TAG.meta $V/$TAG.time; tail -c 6000 $V/$TAG.out
