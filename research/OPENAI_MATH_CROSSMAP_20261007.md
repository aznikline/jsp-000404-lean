# OPENAI-MATH-CROSSMAP-01: OpenAI math collection vs JSP-000404

**Verdict: `NO_DIRECT_REUSE`.** No result in the collection changes the JSP-000404
main proof route. No candidate was promoted. No `Jsp000404/DevinOpenAIMath*.lean`
adapter was written. No JSP Lean source was changed.

This was a bounded side task. It does not replace the JSP404 proof mainline.

## Baselines

| Item | Value |
|---|---|
| External repo | https://github.com/openai/math |
| External SHA (checked out) | `adc7f1241b42e322a6451854ab7e4b4c146bf78a` (Initial commit, 2026-10-06) |
| External toolchain / mathlib | `leanprover/lean4:v4.34.1` / mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| JSP base | `aznikline/jsp-000404-lean` `bd120994b033f7e8e92ff779b795d00db305110c` |
| JSP toolchain / mathlib | `leanprover/lean4:v4.34.0` / mathlib `5ed2965256430c3649e86755f9576b54eca72435` |
| Research branch | `agent/devin-openai-crossmap-20261008` |
| External license | Apache-2.0 (`LICENSE`, `lean/LICENSE`; manuscripts list author "OpenAI") |

File hashes (git blob and sha256) are in `research/openai-math-crossmap-01/SOURCE_HASHES.txt`.

## What I read

- **Read in full:** `README.md`, `lean/README.md`, `lean/ComparatorChallenges/README.md`,
  `lean/docs/{087,090,183}.md`, and the Comparator challenge `.lean`/`.json` pairs
  `SymmetricMahlerEquality`, `HalvingLines`, `AtomicGaussian`, `TriangularGaussian`
  and `PlanarPacking.json`.
- **Grep plus the relevant entries only:** `CONTENTS.md` (9169 lines),
  `overview.tex` (859 lines) and `lean/formalization.yaml` (header and grep).
- **087 Lean:** `Mahler/Classification.lean` lines 1–60, 375–420 and 518–546.
  `Mahler/EqualityMedians.lean`: header, declaration list and lines 590–625.
  `Mahler/Medians.lean`: the `HasMetricMedians` definition.
  `Mahler/Faces.lean`: definitions of `IsParallelPair`, `IsMaximalProperFace` and `HasMFaceStructure`.
  `Mahler/Splitting.lean`: declaration list.
- **090 Lean:** `Triangular/GaussianMinorants.lean` in full.
  `Triangular/Basic.lean`: the `HasAtomicConstruction` definition.
  `Triangular/Main.lean`: declaration list.
  `Certificate/AtomicFiniteCertificate.lean` lines 1–40.
  `Certificate/InverseEnclosure.lean`: the `isUnit_of_right_residual` signature.
  Tactic census of `Certificate/`.
- **183 Lean:** `HalvingLines/Activity.lean` lines 1–80.
  `HalvingLines/Sweep.lean`: declaration list and lines 160–305.
  `HalvingLines/Basic.lean` and `HalvingLines/Model.lean`: headers.
  Declaration lists of `Batches`, `Directions` and `AtomicBounds`.
- **Preprint prose:** only `A-power-saving-for-planar-halving-lines.../build/sections/finite.tex`
  lines 120–140 (the exchange-edge paragraph).
- **Not read:** no PDFs were read in full, and none of the other 719 manuscripts were opened.
  I did not build the whole external library.
- **JSP side:** `Statement.lean` header, `Section4Legality.lean`,
  `ActualCapacityFromCardinality.lean`, `ActualProjectionOrder.lean`, the
  `Deletion.potential` definition and the `GeometricDeletion.directionRows` definition.
  I did not edit any of these.

## 1. Direct-match search: no match

The commands and raw output are in `research/openai-math-crossmap-01/direct_match_search.txt`.

- **`sendov`, `minimax angle`, `maximum angle`, `max-angle`, `angular capacity`, `largest angle`:**
  0 hits in the md, tex, yaml, lean and bib files of the whole repo.
- **`Blumenthal`:** the only hits are citations of A. Blumenthal (dynamics) in
  *Positive Metric Entropy for the Standard Map*. This is a different person and an unrelated problem.
- **`obtuse`:** the Lean hits are in `OAI/Probability/GaussianPropeller` (family 096),
  where the field `obtuse : Pairwise (fun j l => ⟪z j, z l⟫ < 0)` is a sign condition on
  vectors. There is also one prose hit in a lattice-tiling section of the *Uniform marked
  polygon estimates* preprint. Neither is an angle determined by three points of a
  configuration.
- **Planar discrete-geometry families, judged by heading only:** 166/167 (distinct distances),
  172 (Euclidean Ramsey), 183 (halving lines), 191 (Heilbronn triangle *area*) and
  096 (Gaussian propeller sectors). None defines the Blumenthal–Sendov extremal angle
  α(N), and none has a statement about the maximum angle among N planar points.

So the search turned up no direct match. I then deep-read the three allowed families. As
instructed, I did not prioritise 118 (bin packing).

## 2. Candidate cards

### 2.1 Family 087: symmetric Mahler equality and linear Hanner classification

- **SOURCE_SHA:** `adc7f1241b42e322a6451854ab7e4b4c146bf78a`
- **SOURCE_FILE:** `lean/OAI/Analysis/Mahler/Classification.lean`, plus
  `EqualityMedians.lean`, `Medians.lean` and `Faces.lean`.
  - The Comparator JSON (`SymmetricMahlerEquality.json`) sets `solution_module` to
    `OAI.Analysis.Mahler.Classification` and the theorem to
    `OAI.SymmetricMahler.symmetric_mahler_equality`.
  - The challenge `.lean` file ends in `sorry`, as expected. The real proof is at
    `Classification.lean:534` and goes through `equality_implies_linearHanner`.
- **EXACT_LEMMA:**
  `norm_add_of_split (hmed : HasMetricMedians E) (hK : IsMaximalProperFace (closedBall 0 1) K) (p : IsSplitPair K F G) (hFn : F.Nonempty) (hGn : G.Nonempty) : Nonempty (LDecomposition E)`.
  - `LDecomposition E` means two positive-dimensional subspaces with
    `(left × right) ≃ₗ E` and `‖equiv z‖ = ‖z.1‖ + ‖z.2‖`.
  - Its producer is `RealNormData.medians_of_equality` /
    `equality_polar_gauge_medians` (volume-product equality ⇒ `HasMetricMedians` for
    both the norm and its dual).
  - The recursion is in `median_decomposition` and `hannerSpace_of_medians_rank`.
- **ACTUAL_ASSUMPTIONS:**
  - `E` is a finite-dimensional, nontrivial real normed space.
  - `HasMetricMedians E` is a *global* property: **every** triple `x : Fin 3 → E` has a
    point `m` with `dist (x i) (x j) = dist (x i) m + dist m (x j)` for all `i ≠ j`.
  - `K` is a maximal proper face of the unit ball, and `F`, `G` form a split pair of faces of `K`.
  - The equality that feeds all this is equality in **one** global integral inequality
    (`|K||K°| = 4^n/n!`). It is turned into the all-triples median property through an
    optimal-lift / lens-width argument.
- **Answer to the targeted question** ("can equality in local bounds force a global recursive decomposition?"):
  - Not in the sense JSP needs.
  - Here, global decomposition comes from (a) equality in a *single* scalar functional,
    then (b) a property quantified over *all* triples of the space, then (c) linear
    face/span algebra of a convex unit ball.
  - Equality of a sum of local bounds is never used. The decomposition is a
    linear-subspace splitting with additive norm, not a clustering of finitely many points.
- **JSP404_TARGET:** the open arbitrary-n equality / no-saturation route. One would
  want to force Sendov's recursive two-cluster structure, i.e. saturation of the LOW/HIGH
  capacity bounds on `potential lam (directionRows o e c)` should yield structure.
- **MISSING_BRIDGE:**
  - JSP has no normed space, unit ball, polar body or volume product.
    `Section4Legality` is a finite angle condition on `c : Fin s → Plane₂`, and
    `potential` is a sum of `2^rowScore` with floor-based gap scores.
  - A JSP analogue of `HasMetricMedians` would be a new uniform statement over all triples,
    derived from saturation. Proving that is exactly the open structural theorem; assuming
    it would be assuming the desired decomposition.
  - JSP saturation is equality of a *sum of integer local scores from different rows*.
    Per the known trap, local slacks from different covers cannot be added. So the
    one-functional-equality ⇒ uniform-triple-property step has no counterpart.
- **DEPENDENCY_COST:**
  - Transitive closure of `OAI.Analysis.Mahler.Classification`: 237 OAI modules,
    about 28.4k lines. The source scan found no `sorry`, `native_decide` or `axiom`.
  - It is pinned to Lean v4.34.1 with mathlib `d13f23b`, whereas JSP uses v4.34.0 with
    `5ed2965`, so a port would be needed. Not built.
- **LICENSE/ATTRIBUTION:** Apache-2.0, © OpenAI. Paper: *The symmetric Mahler conjecture
  and its equality cases* (OpenAI, 2026-09-22).
- **VERDICT:** **method reference only.**

### 2.2 Family 090: triangular-lattice optimality and sharp Fourier/Gaussian certificates

- **SOURCE_SHA:** `adc7f1241b42e322a6451854ab7e4b4c146bf78a`
- **SOURCE_FILE:** `lean/OAI/Analysis/Triangular/GaussianMinorants.lean`, plus `Basic.lean`,
  `Main.lean`, `Certificate/AtomicFiniteCertificate.lean` and
  `Certificate/InverseEnclosure.lean`.
  - The JSON files point at `OAI.Analysis.Triangular.Main` /
    `OAI.Analysis.Triangular.GaussianMinorants` and `OAI.Analysis.PlanarPacking.Main`.
    The theorems `sharp_gaussian_minorants_atomic` (Main.lean:75) and
    `sharp_fourier_certificate` (PlanarPacking/Main.lean:32) are present.
- **EXACT_LEMMA:** `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction (α) (hα : 0 < α) : ∃ f : SchwartzMap Plane ℝ`, such that:
  - `f` is radial and `f ≤ gaussian α`;
  - `realFourier f` is real and ≥ 0;
  - `f a = gaussian α a` at nonzero points of `A`;
  - `realFourier f w = 0` at nonzero points of `dualA`;
  - `1 ≤ α → AtomicConstruction α f`.
- **How the certificate is actually *constructed*** (not just consumed):
  - `AtomicConstruction`/`HasAtomicConstruction` fixes two order-20 Hermite interpolation
    blocks `1 − R` and `1 + R`. It requires `IsUnit (1 ∓ R)` and gives explicit finite
    coefficients: `Acoefficient · actualParameter (gaussianZ α)` plus a correction `δ`
    with ℓ¹ < 1e-5, and a summable tail with ℓ¹ < 3e-9.
  - Invertibility is proved in `Certificate/AtomicFiniteCertificate.lean`. A rational
    candidate inverse is supplied, and the residual `E = I − (1∓R)·candidate` is bounded
    entrywise by interval arithmetic (`ResidualPlus00..19`, `ResidualMinus00..19`).
    Then `isUnit_of_right_residual` turns `‖E‖ < 1` into exact invertibility, and
    `B + BE` gives inverse enclosures.
  - Tactic census in `Certificate/`: `decide` 685, `norm_num` 435, `linarith` 41,
    `nlinarith` 22, `positivity` 7. No `native_decide`.
  - So it is rational data, kernel-checked residual bounds, and a perturbation step from
    approximate to exact, with sign conditions done by interval/Bernstein bounds.
- **ACTUAL_ASSUMPTIONS:** a fixed planar lattice `A` and its dual, Gaussian potentials,
  Schwartz class and Fourier transform, and the parameter `α > 0` (the explicit atomic
  construction needs `α ≥ 1`). There is one fixed geometric object, and only the
  continuous parameter varies.
- **JSP404_TARGET:** the actual-certificate route for arbitrary n (the strip
  certificate-existence obligations of the `CertificateIntegration` kind) and the open
  arbitrary-n capacity.
- **MISSING_BRIDGE:**
  - JSP would need a certificate family indexed by the unbounded combinatorial parameter
    `n` and valid for configurations of arbitrary size `s`.
  - The 090 certificate is one object for one lattice. Its positivity relies on Poisson
    summation / Fourier duality, and JSP's floor-score potential over angle gaps has no
    such duality.
  - No LP/SDP dual formulation of JSP capacity exists in the repo for such a certificate to plug into.
  - The finite-certificate technique ("rational candidate + residual < 1 ⇒ exact") does not
    help JSP's finite checks. Those are already exact integer/rational kernel checks, for
    example all 24698 n4 outer words.
- **DEPENDENCY_COST:** 216 OAI modules and about 64.7k lines for `GaussianMinorants`;
  563 modules and about 916k lines for `PlanarPacking.Main`. The source scan was clean.
  It is on the mismatched toolchain. Not built.
- **LICENSE/ATTRIBUTION:** Apache-2.0, © OpenAI. Papers: *An atomic certificate for
  triangular-lattice universal optimality* (2026-09-26) and *A sharp Fourier certificate
  for planar circle packing* (2026-09-23).
- **VERDICT:** **method reference only.**

### 2.3 Family 183: planar halving lines, k-sets and level switches

- **SOURCE_SHA:** `adc7f1241b42e322a6451854ab7e4b4c146bf78a`
- **SOURCE_FILE:** `lean/OAI/Combinatorics/HalvingLines/Activity.lean`, plus `Sweep.lean`.
  - The JSON sets `solution_module` to `OAI.Combinatorics.HalvingLines.Main` and the theorem
    to `OAI.PlanarHalving.power_bounds` (Main.lean:27). The challenge file ends in `sorry`.
- **EXACT_LEMMA**, the smallest exact local direction-event lemma in the family:
  - `Sweep.comparison_persists (p q : Point) (h₀ : s₀ ≤ s) (ht : s ≤ t) (hbefore : projection s₀ q < projection s₀ p) (hafter : projection s p < projection s q) : p.1 > q.1 ∧ projection t p < projection t q`
    with `projection s p = p.2 − s·p.1`. In words: once two points swap order in a
    monotone slope sweep, they never swap back.
  - Corollaries: `exchange_rightward`, and
    `separates_step_distance (hP : Generic P) … (hone : at most one critical slope in (s,t)) : setDistance M N ≤ 1`.
- **ACTUAL_ASSUMPTIONS:**
  - `Point := ℝ × ℝ`.
  - Directions are parameterised by *slope* `s ∈ ℝ`, i.e. a single affine chart of the
    projective line. The sweep is monotone in `s` and has no wraparound through vertical.
  - `comparison_persists` itself has no genericity hypothesis.
  - `separates_step_distance` and the counting results need `Generic P`: `GeneralPosition`
    (no three collinear), injective x-coordinates, pairwise distinct slopes for distinct pairs, and no three-segment
    concurrency.
- **JSP404_TARGET:** actual direction events, orders and charging for arbitrary-size
  configurations. This concerns the rows `directionRows o e c` (sorted `dirRep = linRep (o.oangle e (c j - c i))`
  representatives), the cyclic gaps they define, and deletion merging
  adjacent gaps (`potentialErase`).
- **MISSING_BRIDGE:**
  1. The coordinate change from `ℝ × ℝ` to `EuclideanSpace ℝ (Fin 2)` is routine.
  2. JSP uses `Real.Angle` / `oangle` / `dirRep` on a cyclic `RP¹`; the slope chart breaks
     at vertical. An honest bridge needs a chart cut or a rotation per event window.
  3. Actual JSP geometry does **not** supply `Generic`. `Section4Legality` constrains only
     angles of center triangles. It does not exclude parallel chords or equal
     x-coordinates in any fixed chart, so it does not imply `Generic`.
  4. **No current capacity consumer takes this input.**
     `ActualCapacityFromCardinality.potential_le_of_bare_exclusion` consumes a bare
     `(C+1)`-point exclusion. The F17/F22 and NoSAT lanes consume score/hull/deletion
     facts. A "pairs swap at most once" statement gives none of these.
  5. The counting results (`power_bounds`, `O(n^{4/3−ε})`, nonquantitative constants)
     count halving pairs and separable k-subsets, not floor-gap scores. As instructed,
     they cannot be used as a sharp 5/4 bound or any capacity bound.
  6. The one usable *fact* is elementary (two affine functions of `s` cross at most once).
     JSP already has the order statement it needs in `ActualProjectionOrder`
     (`Up`, `up_or_up`, `up_trans`, `exists_ordered_config`), proved natively for actual
     legal configurations without a genericity premise.
- **DEPENDENCY_COST:** smallest of the three. The `Activity` closure is 3 OAI modules
  (`Model`, `Basic`, `Activity`), 514 lines. `Sweep` is 25 modules / 9.3k lines and `Main`
  is 47 modules / 18.2k lines. Source scan clean. Build evidence is in §4.
- **LICENSE/ATTRIBUTION:** Apache-2.0, © OpenAI. Paper: *A power saving for planar halving
  lines* (OpenAI, 2026-09-25).
- **VERDICT:** **method reference only.**

## 3. Promotion decision

No candidate is promoted. The required chain is: external exact lemma ⇒
definition/premise correspondence ⇒ original actual geometry producer ⇒ current capacity
consumer. It breaks as follows:

| Family | Lemma ⇒ premise correspondence | Actual producer | Capacity consumer |
|---|---|---|---|
| 087 | broken: no normed-space / unit-ball / volume-product object in JSP | none (a uniform-triple property from saturation is the open theorem) | none |
| 090 | broken: single-lattice Fourier certificate vs n-indexed combinatorial capacity | none | none |
| 183 | partial: points and order map with chart and genericity gaps | `ActualProjectionOrder` already covers the order fact natively | **none**: no consumer takes swap-once / k-set data |

Nothing here supplies a missing JSP premise. Using any of it would mean assuming an
abstract decomposition, certificate or capacity as a new premise, which the task forbids.

## 4. Build and audit evidence

Full record: `research/openai-math-crossmap-01/build_evidence.txt`.

- **Family 183 subtree built with the external repo's own pins** (Lean v4.34.1, mathlib
  `d13f23b`, unmodified lakefile/manifest), in an isolated clone:
  - `lake exe cache get` → `CACHE_EXIT=0`.
  - `lake build OAI.Combinatorics.HalvingLines.Activity` → `BUILD_EXIT=0`
    (2026-10-07T18:55:52Z–18:58:35Z). The compiled OAI modules were `Model`, `Basic` and `Activity`.
  - `lake build OAI.Combinatorics.HalvingLines.Sweep` → `SWEEP_BUILD_EXIT=0`
    (22 more OAI modules compiled).
  - Lake had to fetch every package the lakefile requires, but it compiled only the
    targeted OAI subtree.
- **Kernel axiom check** (`lake env lean axcheck.lean`, `AXCHECK_EXIT=0`):
  `Sweep.comparison_persists`, `Sweep.exchange_rightward` and
  `Sweep.separates_step_distance` each depend only on
  `[propext, Classical.choice, Quot.sound]`.
  - This shows the 183 lemmas are genuine. It does **not** make them applicable to JSP (§2.3).
- **No JSP-side compilation:** no adapter was written, so nothing was compiled under JSP's
  v4.34.0 / `5ed2965` pins, and no JSP file changed.

- The Comparator challenge files for 087 (`SymmetricMahlerEquality.lean`) and 183
  (`HalvingLines.lean`) contain `sorry` by design. I followed the JSON to the actual
  `solution_module` and theorems listed above and checked that those declarations exist.
- `subtree_scan.txt` records the transitive OAI import closures and a source-level scan for
  `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by` and `@[extern]`.
  There were 0 hits in all six closures.
  - This is a source scan, **not** a kernel axiom closure.
  - The `permitted_axioms` lists in the JSON were **not** treated as verification.
- I did not run Comparator, and I did not build the 087/090 subtrees (no promotion,
  heavy dependency cost).

## 5. Effect on the main proof

- **The main route does not change.** The remaining targets (actual F17 LOW mandatory
  hull-zero deletion selection, F22 six-point mixed tails and their R2 assembly, and the
  arbitrary n ≥ 4 no-saturation / equality / cover / actual-certificate routes) get no
  premise from families 087, 090 or 183.
- **Unresolved bridges, stated honestly:**
  1. Saturation ⇒ a uniform all-triples structural property of the actual configuration
     (the 087 analogue). This is open and is the core theorem itself.
  2. An n-indexed certificate family for arbitrary-size actual configurations (the 090
     analogue). Open, and no dual formulation exists.
  3. A capacity consumer for direction-event / swap-order data (the 183 analogue). None
     exists. The order fact is already native in `ActualProjectionOrder`.
- **Method notes only, not dependencies:**
  - 087: global structure came from a property quantified over all triples, not from summed local equalities.
  - 090: certificates were built from rational candidates plus kernel-checked residual bounds below 1.
  - 183: crossings in a monotone sweep are irreversible.
