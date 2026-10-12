#!/bin/bash
cd /home/ubuntu/work/r1-interfaces-20261012
V=verification/r1-interfaces-20261012; G=/home/ubuntu/work/r1/verification/cache-transfer/lead-resume/linux-guard.py; L=/home/ubuntu/.elan/bin/lake; O=.lake/build/lib/lean/Jsp000404
run() { tag=$1; shift; python3 $G --log $V/logs/$tag.log --cwd $PWD --pss-gib 8 --wallmax 180 --cmd $L env lean -j1 -M8192 "$@"; rc=$?; echo "$(date -u +%FT%TZ) $tag rc=$rc" | tee -a $V/logs/exits.txt; return $rc; }
run 60b_S7N7Core_v2_normal_retry1 -o $O/S7N7Core.olean -i $O/S7N7Core.ilean Jsp000404/S7N7Core.lean && run 61_S7N7Core_v2_strict --trust=0 Jsp000404/S7N7Core.lean && run 62_audit_S7N7Core_v2_strict --trust=0 $V/probe/Audit_S7N7Core.lean; echo "S7RETRY rc=$?"
