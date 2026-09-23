# MAXGAP-EMISSION-02 spec audit — `maxGap_boundary_emission`

Date: 2026-09-22.  Branch: `agent/jsp404-maxgap-emission-02-spec-audit`.
Scope: audit + refreeze the quantifier domain only.  **No proof of any
repaired statement is claimed or attempted.**

## 1. The statement under audit

`Jsp404.maxGap_boundary_emission` (`Jsp000404/GeometricDeletion.lean`,
near line 624) currently carries `sorry`.  As quantified — arbitrary
`s`, arbitrary `lam > 0` — it is **false**.  Its conclusion is a
three-way disjunction:

- **D1** `1 ≤ rowGain lam (directionRow a) (deleteIndex t a)` —
  a positive-gain arc from the max-gap vertex `t` into boundary
  center `a`;
- **D2** the same with `b`;
- **D3** `∃ i v, i ≠ v ∧ 1 ≤ rowGain (row i) (del v i) ∧
  exponentAt v ≤ exponentAt i` — a non-ascending emission arc
  (`CertA` witness shape).

The hypotheses describe `G` as a global maximum cyclic gap realized
in row `t` between the directions to `a` and `b` (`hgap`), maximality
inside row `t` (`hadj`), and `G` bounding every row's minimum
successor gap (`hglob`).

## 2. The four obstruction classes

| # | Class | Status | Mechanism | File |
|---|---|---|---|---|
| 1 | `s = 2` | unconditional, checked | singleton rows ⇒ every `rowGain = 0`; hypotheses satisfiable with `a = b`, `G = 0` | `MaxGapCountermodel.lean` (`maxGap_boundary_emission_countermodel_s2`, `maxGap_boundary_emission_false_s2`) |
| 2 | `lam > π/2` | lemma only, NOT a countermodel by itself | all cyclic gaps `≤ π`, so `⌊g/lam⌋₊ ≤ 1` and all `rowGain`s vanish (`rowGain_eq_zero_of_half_pi_lt`) | `MaxGapCountermodel.lean` |
| 3 | `s = 3`, `lam > π/2` | conditional (given `Section4Legality`), checked | hypotheses instantiable on *every* legal 3-config (put `G` at the vertex maximizing `rowMaxGap3`); then class 2 kills all disjuncts | `MaxGapCountermodel.lean` (`maxGap_boundary_emission_countermodel_s3`) |
| 4 | `s = 4`, `lam = 5π/12` | unconditional, checked | square `0, e, e+w, w`; rows `{0,π/4,π/2}` / `{0,π/2,3π/4}`; all post-deletion gaps `< 2·lam = 5π/6` ⇒ all `rowGain = 0`; hypotheses hold with `t=0, a=3, b=1, G=π/2` | `MaxGapCountermodel2.lean` (`maxGap_boundary_emission_countermodel_s4`, `maxGap_boundary_emission_false_s4`) |

Class 2 is recorded because it is the *mechanism* behind class 3, but it
is a statement about gains, not a geometric countermodel: the hypotheses
of the theorem could in principle be uninstantiable in that regime.

Class 4 is the load-bearing new result: it sits in the **low regime**
(`⌊π/lam⌋₊ = 2`, `δ = π/lam − 2 = 2/5 < 1/2`) at the smallest size the
consumer cares about.

## 3. What the square does and does not refute

- It **refutes** the bare statement, and every repair whose only added
  hypothesis is `4 ≤ s` (or `lam ≤ π/2`, `lam < π/2`, low regime, etc.):
  the square is a legal `s = 4` configuration with `lam = 5π/12`.
- It does **not** refute the consumer-domain repair: the square is flat
  (`Flat`, every `exponentAt = 0`), so `potential = 4 = sendovCap 2
  false` — it lies *at* the cap, and `CertExists` only asks for the
  dichotomy when `sendovCap n big < potential`
  (`sq_potential_eq`, `sq_not_over_cap`).

## 4. Consumer-impact analysis of the three disjuncts

The consumer chain is:

```
maxGap_boundary_emission  --(intended, not yet wired)-->  EmissionDichotomy
  → certA_or_C_of_dichotomy → removable_of_dichotomy → CertExists
  → potential_le_sendovCap (Induction.lean)
```

`CertExists n big lam` (`Induction.lean`) asks for `EmissionDichotomy`
on legal `c : Fin t → Plane₂` with `4 ≤ t` and `sendovCap n big <
potential lam (directionRows o e c)` only.

| Disjunct | Shape | Role for `EmissionDichotomy` | Status on square |
|---|---|---|---|
| D1 | `1 ≤ rowGain (row a) (del t a)` | positive-gain arc `t → a` into a boundary center of the max gap; becomes a `CertA` arc at victim `t` iff `exponentAt a ≥ exponentAt t`, otherwise it is an upward arc for the charge-bookkeeping branch | fails (`rowGain = 0`) |
| D2 | `1 ≤ rowGain (row b) (del t b)` | symmetric boundary arc `t → b` | fails (`rowGain = 0`) |
| D3 | `∃ i v, i ≠ v ∧ 1 ≤ rowGain (row i) (del v i) ∧ exponentAt v ≤ exponentAt i` | **literally** the left disjunct of `EmissionDichotomy` — a `CertA` witness | fails (no positive-gain arc exists at all) |

Nothing in the tree currently *calls* `maxGap_boundary_emission` — it is
the isolated geometric crux for the still-open `CertExists` premise.
D3 is the disjunct with a direct consumer (`EmissionDichotomy` left);
D1/D2 are the boundary-arc inputs that the intended argument routes
through the `CertA/CertB/CertC` bookkeeping layer
(`partner_exponent_lt_of_not_certA` etc.) when the boundary exponent
comparison fails.

On a flat configuration every `exponentAt` is `0`, so *any* positive-gain
arc is automatically a `CertA` arc — flat configs need only one
emitting deletion.  The square is flat *and* gain-free; flatness alone
does not imply gain-freeness (`rowGain` is a difference of two erased-
row scores, both potentially positive), so class-4-style failures are
exactly the "flat, at-or-over-cap, no-emitting-vertex" corner.

## 5. Candidate repaired domain — NOT PROVED

The only domain consistent with all checked countermodels is the
consumer's own domain:

```lean
-- CANDIDATE REPAIR — status: stated for audit only, no proof claimed.
theorem maxGap_boundary_emission_overCap
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {s : ℕ}
    {c : Fin s → Plane₂} {lam : ℝ}
    (hlegal : Section4Legality c lam) (he : e ≠ 0)
    (hs : 4 ≤ s) {n : ℕ} {big : Bool}
    (hover : sendovCap n big <
      potential lam (directionRows o e c))
    {t a b : Fin s} {G : ℝ}
    (hta : t ≠ a) (htb : t ≠ b)
    (hgap : cyclicDiff (dirRep o e c t a)
              (dirRep o e c t b) = G)
    (hadj : ∀ z ∈ directionRow o e c t, z ≠ dirRep o e c t a →
              G ≤ cyclicDiff (dirRep o e c t a) z)
    (hglob : ∀ i : Fin s, ∀ x y : ℝ,
              x ∈ directionRow o e c i → y ∈ directionRow o e c i →
              (∀ z ∈ directionRow o e c i, z ≠ x →
                cyclicDiff x y ≤ cyclicDiff x z) →
              cyclicDiff x y ≤ G) :
    (1 ≤ rowGain lam (directionRow o e c a)
          (deleteIndex o e c t a)) ∨
    (1 ≤ rowGain lam (directionRow o e c b)
          (deleteIndex o e c t b)) ∨
    (∃ i v : Fin s, i ≠ v ∧
      1 ≤ rowGain lam (directionRow o e c i)
        (deleteIndex o e c v i) ∧
      exponentAt lam (directionRows o e c) v ≤
        exponentAt lam (directionRows o e c) i)
```

In the actual consumer `n = ⌊π/lam⌋₊` and `big ↔ δ ≥ 1/2`, so `hover`
says exactly "this configuration is over the Sendov cap" — the region
where the induction needs a certificate.

### Known issues with this candidate (documented, unresolved)

- **`¬Flat` is not implied by the premise in general.**  `Flat` gives
  `potential = s`; the premise `sendovCap n big < potential` excludes
  flat configs only when `s ≤ sendovCap n big`.  For `s > 2^n` a flat
  config would still satisfy `hover`, and if it had no emitting
  deletion it would refute even this repair.  Whether such
  "large flat" legal configurations exist is open; any proof of the
  candidate must include a flat-large-`s` gain argument or exclude
  that region explicitly.
- **Non-circularity requirement.**  `potential ≤ sendovCap n big` is
  precisely the bound `potential_le_sendovCap` is proving.  The
  candidate may use `hover` as a *hypothesis*, but its proof must not
  invoke the capacity bound (or `CertExists`) — the whole point is to
  supply `CertExists`, so any capacity-based argument would be
  circular.
- **D1/D2 vs D3 asymmetry.**  A proof need not deliver all three
  disjuncts in the shape stated; what `EmissionDichotomy` strictly
  needs is D3, or boundary arcs plus the exponent bookkeeping.  Any
  re-statement should record which disjuncts the consumer proof uses.

## 6. Verification record

- `MaxGapCountermodel2.lean` builds clean under
  `lake build Jsp000404.MaxGapCountermodel2`; no `sorry`.
- `#print axioms` (in-file, lines ~726–731):
  `maxGap_boundary_emission_countermodel_s4`,
  `maxGap_boundary_emission_false_s4`, `rowGain_sq_zero`,
  `sq_legal`, `sq_potential_eq`, `sq_not_over_cap` each depend only on
  `[propext, Classical.choice, Quot.sound]`.
- `maxGap_boundary_emission` itself still contains `sorry` at
  `GeometricDeletion.lean`; that is pre-existing and out of scope —
  this audit does not attempt a proof of any repaired statement.
