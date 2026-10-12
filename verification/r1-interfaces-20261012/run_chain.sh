#!/bin/bash
# serial guarded chain; stops at first non-zero exit
cd /home/ubuntu/work/r1-interfaces-20261012
V=verification/r1-interfaces-20261012; G=/home/ubuntu/work/r1/verification/cache-transfer/lead-resume/linux-guard.py; L=/home/ubuntu/.elan/bin/lake; O=.lake/build/lib/lean/Jsp000404
run() { tag=$1; shift; python3 $G --log $V/logs/$tag.log --cwd $PWD --pss-gib 8 --wallmax 180 --cmd $L env lean -j1 -M8192 "$@"; rc=$?; echo "$(date -u +%FT%TZ) $tag rc=$rc" | tee -a $V/logs/exits.txt; [ $rc -eq 0 ] || { echo CHAIN_STOP $tag; exit $rc; }; }
run 11_S8Defs_normal -o $O/S8Defs.olean -i $O/S8Defs.ilean Jsp000404/S8Defs.lean
run 20_S7N7Core_normal -o $O/S7N7Core.olean -i $O/S7N7Core.ilean Jsp000404/S7N7Core.lean
run 21_S7N7Core_strict --trust=0 Jsp000404/S7N7Core.lean
run 30_S8N8Core_normal -o $O/S8N8Core.olean -i $O/S8N8Core.ilean Jsp000404/S8N8Core.lean
run 31_S8N8Core_strict --trust=0 Jsp000404/S8N8Core.lean
run 40_audit_S7N7Core_strict --trust=0 $V/probe/Audit_S7N7Core.lean
run 41_audit_S8N8Core_strict --trust=0 $V/probe/Audit_S8N8Core.lean
echo CHAIN_DONE
