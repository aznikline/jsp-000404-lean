import Jsp000404.GadgetSelection
import Mathlib.Data.Fin.VecNotation

/-!
# Gadget fixtures — checker-discovered certificates replayed in Lean

Each fixture encodes a concrete skeleton (vertex orders, bits,
q-cells) together with a concrete gadget and verifies its validity
and bound.  These are the Lean counterparts of the certificates
found by `tools/lane_a6.py` (extended-cap evaluator).

## Fixture 1 — the vertex-floor certificate

Skeleton `idxs = (0, 93, 75, 50)` of the `s = n = 4` deficit profile
`(k_v) = (3,2,2,1)` (`W = 9/4 > 2`).  The mode-A LP proves
`δ_min = 1`, i.e. the skeleton is a *phantom* (infeasible for
`δ < 1`), and the extracted Farkas certificate is a pure
single-vertex combination at vertex `2`:

    ∠₂₀₁ ≤ π−λ :  r₂₀ + r₂₁ ≤ δ      (direct arc {g₀,g₁}, q = 3)
    ∠₂₀₃ ≤ π−λ :  r₂₀ ≥ 1            (complementary arc {g₀}, q = 0)
    r₂₁ ≥ 0                          (absorbed by `r_nn`)

giving `0 ≤ −1 + δ`.  In gadget form this is a cap combination on
the *empty* negative block — a vertex floor — which requires the
Lane-A `CapKind.low` entry: the old cap grammar cannot express it.

Vertex data below (self-positions/bits are unused dummies):

* `v0`: order `(1,2,3)`, bits `000`, `q = (0,0,4)`
* `v1`: order `(0,3,2)`, bits `b3=b2=1`, `q = (3,0,0)`
* `v2`: order `(0,3,1)`, bits `b3=1`,   `q = (0,3,0)`
* `v3`: order `(0,2,1)`, bits `000`,   `q = (0,2,0)`
-/

namespace Jsp404

/-- The phantom skeleton `(0,93,75,50)`. -/
def phantomSk : Skeleton 4 where
  vtx := fun v => match v with
    | 0 => ⟨![0, 0, 1, 2], ![false, false, false, false], ![0, 0, 4]⟩
    | 1 => ⟨![0, 0, 2, 1], ![false, false, true, true], ![3, 0, 0]⟩
    | 2 => ⟨![0, 2, 0, 1], ![false, false, false, true], ![0, 3, 0]⟩
    | _ => ⟨![0, 2, 1, 0], ![false, false, false, false], ![0, 2, 0]⟩

/-- The floor gadget: no equalities, two signed cap entries at
vertex `2` whose combined coverage is `(α₀,α₁,α₂) = (0,1,0) ≥ 0`
with constant `0 + (−1) = −1` and δ-coefficient `1`. -/
def phantomFloor : Gadget 4 where
  fans := fun _ => 0
  links := []
  charges := []
  caps := [⟨2, .piLam, 0, 1, 0, 1⟩,
           ⟨2, .low, 0, 3, 0, 1⟩]

/-- The floor gadget is valid — the certificate `δ ≥ 1` exists only
because of the Lane-A `low` cap kind. -/
theorem phantomFloor_valid :
    phantomFloor.Valid 4 phantomSk := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · intro l hl
    cases hl
  · intro e he
    cases he
  · exact List.Pairwise.nil
  · intro e he
    rcases List.mem_cons.mp he with rfl | h
    · exact ⟨by decide,
        ⟨by decide, by unfold VertexData.comp; decide⟩⟩
    · rcases List.mem_singleton.mp h
      exact ⟨by decide,
        ⟨by decide, by unfold VertexData.comp; decide⟩⟩
  · native_decide
  · native_decide

/-- Its bound is `1`: `(K − Bcap − CC)/(cc + uu) = (0+1)/1`. -/
theorem phantomFloor_bound :
    phantomFloor.bound 4 phantomSk = 1 := by
  native_decide

/-- The score-≥1 conclusion of `GadgetSelectionLow` is met. -/
theorem phantomFloor_score :
    (1 : ℚ) / 2 ≤ phantomFloor.bound 4 phantomSk := by
  native_decide

end Jsp404
