# R1-GEOMETRY-CORES-03 v2 (interface audit only: not the T2 terminal, not a complete JSP404; sendov_lower OPEN)
Base f17a5ed; inputs are frozen AIR f818584 (manifest 0e05d3ad…). Guard limits unchanged (8GiB / 180s / -j1).
- S7N7Core PASS: normal (retry after PSS exit race) + --trust=0; all 26 source-public decls (+ auto n7T.congr_simp) print Std3.
- S8N8Core PASS: normal 6.707 GiB (bytes/1024^3) / 9.4s + --trust=0; all 26 source-public decls (+ auto n8T.congr_simp) print Std3.
- New S8ScoreArithmetic (no imports; all 28 + 7 branches over Nat): normal + strict; axioms [propext, Quot.sound].
- S7N7Defs = frozen S7Defs bytes. S7Defs is now a shell (Mathlib + S7N7Defs + S8Defs); a smoke probe #checks all 78 old names.
- v1 failures (S8Defs wall limit, S8N8Core PSS 8.61GiB, ℕ notation without Mathlib) are kept in logs/ and edit_ledger.log.
- The ~208 downstream importers of S7Defs were not rebuilt.
- ROOT INDEPENDENT ACCEPTANCE PASSED at ebc6f11: for both cores normal + --trust=0 exit 0, and full-api probes (26 + 26 public declarations) print Std3 only.
  Peak PSS: S7 normal 7828604928 B (7.291 GiB), S8 normal 7170038784 B (6.678 GiB); all <= 8*1024^3 B, all <= 21 s.
  root-S8N8Core-full-api-attempt2 hit MONITOR_FAILED (PSS exit race). It is kept and not counted; retry1 is the accepted run.
- Unit fix: S8Defs peak is 4034376704 B = 3.757 GiB, S7Defs/S7N7Defs 2924983296 B = 2.724 GiB (earlier "4.03 GB"/"2.92 GB" were decimal GB).
- probe/S8N8CoreSlice_F{1,2}.lean.txt are DIAGNOSTIC_NOT_PROOF (they contain sorry on purpose; see probe/DIAGNOSTIC_NOT_PROOF.md).
- Still OPEN: complete JSP404, sendov_lower, the seven-point T2 terminal.
- Root independent name-set check: in each full-api log, regex `'(name)' depends on axioms: [list]` gives 26 names, equal to the frozen source list (S7 26/26, S8 26/26), Std3 only. The 27th entry in our audits 62/72 is the auto-generated n7T/n8T.congr_simp, not a missing source public.
