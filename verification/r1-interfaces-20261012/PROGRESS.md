# R1-GEOMETRY-CORES-03 v2 (interface audit only: not the T2 terminal, not a complete JSP404; sendov_lower OPEN)
Base f17a5ed; inputs are frozen AIR f818584 (manifest 0e05d3ad…). Guard limits unchanged (8GiB / 180s / -j1).
- S7N7Core PASS: normal (retry after PSS exit race) + --trust=0; all 26 source-public decls (+ auto n7T.congr_simp) print Std3.
- S8N8Core PASS: normal 6.71GiB / 9.4s + --trust=0; all 26 source-public decls (+ auto n8T.congr_simp) print Std3.
- New S8ScoreArithmetic (no imports; all 28 + 7 branches over Nat): normal + strict; axioms [propext, Quot.sound].
- S7N7Defs = frozen S7Defs bytes. S7Defs is now a shell (Mathlib + S7N7Defs + S8Defs); a smoke probe #checks all 78 old names.
- v1 failures (S8Defs wall limit, S8N8Core PSS 8.61GiB, ℕ notation without Mathlib) are kept in logs/ and edit_ledger.log.
- The ~208 downstream importers of S7Defs were not rebuilt.
