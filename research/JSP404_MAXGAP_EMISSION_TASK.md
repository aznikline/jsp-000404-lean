# JSP404-MAXGAP-EMISSION-01 — Owner Task

## Mission

Prove `maxGap_boundary_emission`, the single `sorry` at
`Jsp000404/GeometricDeletion.lean:629`, on the current integration
trunk. It is the declared last geometric input to `EmissionDichotomy`,
which is the only remaining mathematical blocker (`CertExists`) for
`sendov_lower` at N ≥ 9 — i.e. the last node of JSP-000404.

## Repository / base

- Repo: `aznikline/jsp-000404-lean`
- Base commit: `0ceac4df4018b2d14a38c0766e742b234a09489b`
  (current `lane/integration` / `goal/jsp404-completion` HEAD)
- Suggested branch: `lane/h-general-high-p1` or
  `agent/jsp404-maxgap-emission-01-owner`
- Do NOT base on `8581318` (the older `lane/h-general-high` task doc's
  base is stale; the trunk already merged the angle-cert material it
  told you to port).
- Do NOT touch `exists_removable_vertex` /
  `exists_removable_hull_vertex` in `Deletion.lean` — they are
  deprecated and provably false as stated (missing sortedness /
  index-range hypotheses).

## The statement (verbatim, keep it)

```lean
theorem maxGap_boundary_emission {lam : ℝ} (hlegal : Section4Legality c lam)
    (he : e ≠ 0) {t a b : Fin s} {G : ℝ}
    (hta : t ≠ a) (htb : t ≠ b)
    (hgap : cyclicDiff (dirRep o e c t a) (dirRep o e c t b) = G)
    (hadj : ∀ z ∈ directionRow o e c t, z ≠ dirRep o e c t a →
      G ≤ cyclicDiff (dirRep o e c t a) z)
    (hglob : ∀ i : Fin s, ∀ x y : ℝ,
      x ∈ directionRow o e c i → y ∈ directionRow o e c i →
      (∀ z ∈ directionRow o e c i, z ≠ x →
        cyclicDiff x y ≤ cyclicDiff x z) →
      cyclicDiff x y ≤ G) :
    (1 ≤ rowGain lam (directionRow o e c a) (deleteIndex o e c t a)) ∨
    (1 ≤ rowGain lam (directionRow o e c b) (deleteIndex o e c t b)) ∨
    (∃ i v : Fin s, i ≠ v ∧
      1 ≤ rowGain lam (directionRow o e c i) (deleteIndex o e c v i) ∧
      exponentAt lam (directionRows o e c) v ≤
        exponentAt lam (directionRows o e c) i)
```

Semantics:

- `G` is the **global maximum cyclic gap** over all direction rows.
  `hglob` says every cyclic gap in every row is `≤ G`.
- It is realized at center `t` between the directions to `a` (start)
  and `b` (end): `hgap` gives the gap value and `hadj` says `dirRep t b`
  is the successor of `dirRep t a` in `t`'s row (every forward arc from
  `dirRep t a` is ≥ G), i.e. `a`,`b` are consecutive directions with the
  empty wedge of size `G` between them.
- Conclusion: either boundary center `a` or `b` *emits* to `t`
  (`rowGain ≥ 1` when `t` is deleted from that row), or a down/level
  arc exists somewhere (a `CertA` witness).

## Proof machinery already in the same file (use it)

- `rowGain_eq_mergeGain`: `rowGain` = merge gain of the two incident
  cyclic gaps at the deleted position.
- `rowGain_pos_of_gaps_ge` / `rowGain_pos_of_forall_dirRep_dist`:
  both incident gaps `≥ λ` ⇒ `rowGain ≥ 1`.
- `rowGain_pos_of_forall_angle_ge`: if every ray `i→j` (`j ≠ v`) makes
  `∠(c v, c i, c j) ≥ λ`, then `rowGain i (del v) ≥ 1`. The upper bound
  `∠ ≤ π − λ` comes from `hlegal.triAngle`.
- `emit_or_near_collinear`: either `i` emits to `v`, or ∃ `j` with
  `∠(c v, c i, c j) < λ` — a near-collinearity witness. This is the
  contrapositive engine: assume both boundary emissions fail and
  collect two witnesses `j_a`, `j_b`.

## Mechanism sketch (from the file comment + checker evidence)

Checker-validated on ~10⁵ legal non-flat samples (`beNnoA = 0`): it
never happens that both boundary centers fail to emit to `t` while no
down/level arc exists anywhere. The unconditional statement is believed
true.

When both boundaries fail (`N`-case), each failure gives a
near-collinear witness: some `j` with `∠(t,a,j) < λ` (and likewise at
`b`). The failure is a lattice-alignment condition — the near-side gap
and the huge gap `G` cannot both fit inside `λ`-multiples — and the
escape is always a down/level arc elsewhere, or an interior emitter
into `t` itself (every sampled config has `t` receiving a
positive-gain arc; `tRecv0 = 0`).

Intended argument shape:

1. Suppose disjuncts 1–2 fail. By `emit_or_near_collinear`, get
   `j_a` with `∠(t,a,j_a) < λ` and `j_b` with `∠(t,b,j_b) < λ`.
2. Use the gap geometry: the wedge `a → b` at `t` is empty and `G` is
   the global max — no cyclic gap anywhere exceeds `G`. Transport the
   witnesses' small angles through the fan structure at `a`, `b`, `t`.
3. Show the forced configuration yields either a positive-gain arc
   into `t` from an interior center (which is `rowGain ≥ 1`, i.e.
   disjunct 1 or 2 again — contradiction) or a non-ascending arc
   `i → v` (disjunct 3).
4. Exponent comparison for disjunct 3: `exponentAt v ≤ exponentAt i`
   follows from the arc not climbing the `⌊gap/λ⌋` ladder — use the
   `gapScore`/`mergeGain` lemmas in `Deletion.lean`.

## Second stage (attempt, but stage 1 is the deliverable)

After 629 is proved, try to assemble `EmissionDichotomy` for an
arbitrary legal config: pick the global max gap (exists — finite
rows), instantiate `t, a, b, G`, apply the theorem, and convert
disjuncts 1–2 into dichotomy material. Watch out: a positive-gain arc
`a → t` is `CertA` only if `exponentAt t ≤ exponentAt a`; ascending
arcs need the `potential > sendovCap` hypothesis or extra structure —
if the assembly genuinely requires over-cap, document exactly where it
enters rather than hiding it.

## Acceptance

- `maxGap_boundary_emission` proved, `sorry`-free, arbitrary `s`
  (do not specialize to `s = 4` or convex position).
- `#print axioms` on it and any new exported theorem: only
  `propext`, `Classical.choice`, `Quot.sound`.
- `lake build` green (the merge worktree at
  `/Users/wizout/op/learn/sunyuchen/jsp-wt-merge` already has a full
  `.lake` cache if you want to work there — it is on
  `lane/integration` = `0ceac4d`).
- No `sorry`/`admit`/`native_decide`/custom axioms.

## Escalate (do NOT patch around)

Stop and report if:

1. The statement is false as written (e.g. `hadj`/`hglob` do not
   capture "global max gap realized at t with consecutive endpoints",
   or a counterexample needs an over-cap / non-degeneracy hypothesis).
   Produce the countermodel explicitly.
2. The conclusion is provable only in a weaker form — report the
   strongest proved form with the exact gap.
3. Proving it requires modifying `Section4Legality` or the
   `directionRow`/`dirRep`/`cyclicDiff`/`deleteIndex` contracts.

## Delivery

Commit + push to the branch. Report must include:

```
REMOTE_BRANCH / REMOTE_EXACT_HEAD / BASE_SHA / FILES_CHANGED
TEST_COMMANDS / TEST_RESULTS
THEOREMS_PROVED / AXIOM_OUTPUT
MAXGAP_STATUS = PROVED/WEAKENED/FAILED/BLOCKED
ASSEMBLY_STATUS = PROVED/PARTIAL/NOT_ATTEMPTED
COUNTEREXAMPLES_OR_BLOCKERS
```

Research/status notes go under `research/` in the repo.
