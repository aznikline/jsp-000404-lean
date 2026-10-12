#!/bin/bash
cd /home/ubuntu/work/r1-interfaces-20261012
V=verification/r1-interfaces-20261012; G=/home/ubuntu/work/r1/verification/cache-transfer/lead-resume/linux-guard.py; L=/home/ubuntu/.elan/bin/lake; O=.lake/build/lib/lean/Jsp000404
run() { tag=$1; shift; python3 $G --log $V/logs/$tag.log --cwd $PWD --pss-gib 8 --wallmax 180 --cmd $L env lean -j1 -M8192 "$@"; rc=$?; echo "$(date -u +%FT%TZ) $tag rc=$rc" | tee -a $V/logs/exits.txt; return $rc; }
s8() { run 50b_S8ScoreArithmetic_v1_normal -o $O/S8ScoreArithmetic.olean -i $O/S8ScoreArithmetic.ilean Jsp000404/S8ScoreArithmetic.lean || return 1
 run 51b_S8ScoreArithmetic_v1_strict --trust=0 Jsp000404/S8ScoreArithmetic.lean || return 1
 run 52b_audit_S8ScoreArithmetic_v1_strict --trust=0 $V/probe/Audit_S8ScoreArithmetic.lean || return 1
 run 70_S8N8Core_v2_normal -o $O/S8N8Core.olean -i $O/S8N8Core.ilean Jsp000404/S8N8Core.lean || return 1
 run 71_S8N8Core_v2_strict --trust=0 Jsp000404/S8N8Core.lean || return 1
 run 72_audit_S8N8Core_v2_strict --trust=0 $V/probe/Audit_S8N8Core.lean; }
s7() { run 53_S7N7Defs_normal -o $O/S7N7Defs.olean -i $O/S7N7Defs.ilean Jsp000404/S7N7Defs.lean || return 1
 run 54_S7N7Defs_strict --trust=0 Jsp000404/S7N7Defs.lean || return 1
 run 55_S7Defs_shell_normal -o $O/S7Defs.olean -i $O/S7Defs.ilean Jsp000404/S7Defs.lean || return 1
 run 56_S7Defs_shell_strict --trust=0 Jsp000404/S7Defs.lean || return 1
 run 57_smoke_S7Defs_shell --trust=0 $V/probe/Smoke_S7Defs_shell.lean || return 1
 run 60_S7N7Core_v2_normal -o $O/S7N7Core.olean -i $O/S7N7Core.ilean Jsp000404/S7N7Core.lean || return 1
 run 61_S7N7Core_v2_strict --trust=0 Jsp000404/S7N7Core.lean || return 1
 run 62_audit_S7N7Core_v2_strict --trust=0 $V/probe/Audit_S7N7Core.lean; }
s8; echo "S8_GROUP rc=$?"; echo CHAIN_DONE
