# R1-GEOMETRY-CORES-03 (interface audit; not T2 terminal, not complete JSP404; sendov_lower OPEN)
Base f17a5ed; sources = frozen AIR f818584 interface-input bytes (manifest 0e05d3ad…), unchanged. Old S7Defs preserved at snapshots/S7Defs_pre_f17a5ed.lean.
- S7Defs normal: PASS (91.5s, 2.92GB PSS).
- S7N7Core: PASS normal (23.3s, 7.75GB) + --trust=0 (19.2s, 7.61GB); audit (logs/40_*) prints signature + #print axioms for all 27 non-internal decls: all Std3.
- S8Defs normal: attempt1 WALL_LIMIT 180.055s (kept); attempt2 PASS 139.0s, 4.03GB.
- S8N8Core: RESOURCE_BLOCKED. Normal hit PSS_LIMIT 8.61GB at 28s; strict/audit not run. Import-only 6.96GB; peak localised to
  rowSig2_8_of_linearScore_two's `key` by_cases/omega tree (+~1.45GB). Hoisting key to an ℕ lemma (probe v1) still 8.35GB -> rejected.
  Remaining: lower-memory proof of that 28-way ℕ case split (or Root decision on limits). Not attempted further per 3-failure rule.
Caveat: replacing S7Defs at this base drops its old N8 material; see manifest for importer check.
