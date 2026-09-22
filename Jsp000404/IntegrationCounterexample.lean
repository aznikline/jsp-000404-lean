import Jsp000404.Integration

/-!
# A regression check on the old geometric selection interface

Before the integration audit, `GadgetSelection.low` quantified over
all positive lambda, including lambda greater than pi. Two distinct
points then give a counterexample at n = 0. The original signature is
recorded separately here so that correcting the production interface
does not erase the evidence.
-/

namespace Jsp404

def LegacySelectionLow : Prop :=
  ∀ (V : GCfg) (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
      {lam : ℝ} {n : ℕ},
      Section4Legality
        (fun i : Fin V.forest.length => (V.forest.get i).centerOf) lam →
      V.forest.Nodup → Nat.floor (Real.pi / lam) = n →
      Real.pi / lam - (n : ℝ) < 1 / 2 →
      ((exponents V o e lam).map (2 ^ ·)).sum ≤ 2 ^ n

theorem not_legacySelectionLow : ¬ LegacySelectionLow := by
  intro hsel
  classical
  let o : Orientation ℝ Plane₂ (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let e : Plane₂ := EuclideanSpace.basisFun (Fin 2) ℝ (0 : Fin 2)
  have he : e ≠ 0 :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.ne_zero _
  let pts : List Plane₂ := [0, e]
  have hp : pts.Nodup := by simp [pts, Ne.symm he]
  have hl : 2 ≤ pts.length := by simp [pts]
  let V := GCfg.trivial pts hl
  have hf : V.forest.Nodup := trivial_forest_nodup hp hl
  have hlegal : Section4Legality
      (fun i : Fin V.forest.length => (V.forest.get i).centerOf)
      (3 * Real.pi) := by
    apply legality_of_GC V (trivial_disjointCircles hl) hf
      (trivial_centers_distinct hl) (trivial_nonempty hl) (by positivity)
    intro a ha b hb c hc hab hbc hac
    simp only [V, GCfg.trivial_points, pts, List.mem_cons, List.not_mem_nil,
      or_false] at ha hb hc
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      rcases hc with rfl | rfl <;> simp_all
  have hratio : Real.pi / (3 * Real.pi) = 1 / 3 := by
    field_simp
  have hfloor : Nat.floor (Real.pi / (3 * Real.pi)) = 0 := by
    rw [hratio]
    norm_num
  have hw := hsel V o e hlegal hf hfloor (by rw [hratio]; norm_num)
  have hsum (ks : List ℕ) : ks.length ≤ (ks.map (2 ^ ·)).sum := by
    induction ks with
    | nil => simp
    | cons k ks ih =>
      have hk : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_pow k 2 (by omega)
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
  have hlen : (exponents V o e (3 * Real.pi)).length = 2 := by
    simp [exponents, V, GCfg.trivial, pts]
  have := hsum (exponents V o e (3 * Real.pi))
  rw [hlen] at this
  norm_num at hw
  omega

#print axioms not_legacySelectionLow

end Jsp404
