#!/bin/bash
cd /home/ubuntu/work/r1-interfaces-20261012
V=verification/r1-interfaces-20261012; G=/home/ubuntu/work/r1/verification/cache-transfer/lead-resume/linux-guard.py; L=/home/ubuntu/.elan/bin/lake; O=.lake/build/lib/lean/Jsp000404
run() { tag=$1; shift; python3 $G --log $V/logs/$tag.log --cwd $PWD --pss-gib 8 --wallmax 180 --cmd $L env lean -j1 -M8192 "$@"; rc=$?; echo "$(date -u +%FT%TZ) $tag rc=$rc" | tee -a $V/logs/exits.txt; return $rc; }
run 52c_audit_S8ScoreArithmetic_v1_strict --trust=0 $V/probe/Audit_S8ScoreArithmetic.lean
run 70_S8N8Core_v2_normal -o $O/S8N8Core.olean -i $O/S8N8Core.ilean Jsp000404/S8N8Core.lean && run 71_S8N8Core_v2_strict --trust=0 Jsp000404/S8N8Core.lean && run 72_audit_S8N8Core_v2_strict --trust=0 $V/probe/Audit_S8N8Core.lean; echo "S8B rc=$?"
