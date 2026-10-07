# Failed / superseded iterations (pre-receipt)

These were interactive `lake env lean Jsp000404/DevinF17HullGap.lean` runs
(no `--trust=0`) during development of the pure list layer only. Their
intermediate source files were edited in place and were NOT preserved
byte-for-byte; the diagnostics below are copied verbatim from the session
transcript. No geometric or main-theorem iteration failed: those sections
compiled on their first run. All acceptance runs (trust0.log, build.log,
axiom_check.log) are of the final source only.

1. List layer, iteration 1 (exit 0 but with errors reported):
   - `Jsp000404/DevinF17HullGap.lean:125:60: error: Type mismatch
     List.erase_cons_head has type ∀ (a : ?m.378) (l : List ?m.378),
     (a :: l).erase a = l but is expected to have type
     (x :: (m0 ++ [L])).erase x = m0 ++ [L]`
     Fix: `List.erase_cons_head _ _`.
   - `Jsp000404/DevinF17HullGap.lean:202:25: error: Application type mismatch:
     The argument hxL has type ¬x = L but is expected to have type
     ¬(x = L ∨ x ∈ [])` Fix: simp set `List.not_mem_nil, or_false`.
   - warnings: `if_neg`/`if_pos` deprecated (lines 40,42,51,53,139,179).
2. Iteration 2: replaced by `ite_cond_eq_false/true`; compiled with
   deprecation warnings (`ite_cond_eq_false` deprecated: use
   `ite_eq_right_of_eq_false`).
3. Iteration 3: renamed to `ite_eq_right_of_eq_false (eq_false ..)`;
   errors `Tactic rewrite failed: Did not find an occurrence of the pattern
   if ?m then eq_false ?m else ?b` at lines 40, 51, 139 (wrong argument
   shape). Fix: replaced all such rewrites by `split_ifs <;> linarith`.
4. Iteration 4 onward: zero errors, zero warnings.
