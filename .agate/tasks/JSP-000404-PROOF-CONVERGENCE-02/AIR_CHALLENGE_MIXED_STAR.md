# AIR challenge — JSP404-MIXED-STAR-EXCLUSION-01

STATUS: PENDING — no delegation channel available to Owner; not sent.

Target SHA: cd847f3515f170b0c730b407442e9bbfea991fce
Files: Jsp000404/ProjectionDescent.lean, Jsp000404/StarReceiver.lean,
Jsp000404/MixedStarExclusion.lean.

Challenge points (review only, do not re-implement):
1. Lift: `up_of_short_first` / `up_of_short_last` / `up_or_up` — the
   actual oriented angle of each directed edge is derived from
   `linRep_class` + endpoint caps, never assumed.
2. `oangle_add_between`: sign argument, strictness, the hypothesis
   `β < α + π`, and `a + b ≠ 0`.
3. `up_cap`: angle(a,b,c) = π − |φ_bc − φ_ab| requires both upward
   edges; check the `angle_neg_left` step.
4. Five-point rows: `row4_defect` identifies the row list exactly
   (length 3 = s − 1 at s = 4, three distinct chords, sortedness).
5. Mirror: `mixed_star_1F2L_core` is proved separately, not transported.
6. Scope: only full-in stars with all three sources of defect 2 at
   s = 4; no claim about partial receivers, R = 4, or general m.
7. Evidence classes: full-root build 9003 jobs is recorded separately
   from module builds; 55188de did NOT build at full root (name clash).
