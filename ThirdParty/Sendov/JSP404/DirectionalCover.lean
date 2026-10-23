import JSP404.Basic
import JSP404.BinaryEncoding
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# From narrow direction cones to bipartite graph covers

For one direction vector `u`, orient a segment from `v` to `w` when its outgoing
vector makes angle at most `δ` with `u`. If every angle in a configuration is
strictly smaller than `π - 2δ`, a vertex cannot have both an incoming and an
outgoing segment in that cone. Sources and sinks therefore give a two-colouring.

The covering of all directions is an explicit hypothesis of the final counting
theorems. This file does not assume, or assert, the geometric circle-cover lemma.
-/

noncomputable section

namespace JSP404

/-- A directed segment whose direction belongs to a cone of angular radius `δ`. -/
def ConeEdge {V : Type*} (p : V → Point) (u : Point) (δ : ℝ) (v w : V) : Prop :=
  v ≠ w ∧ InnerProductGeometry.angle (p w - p v) u ≤ δ

/-- The undirected graph obtained from the positive and negative direction cones. -/
def coneGraph {V : Type*} (p : V → Point) (u : Point) (δ : ℝ) : SimpleGraph V where
  Adj v w := ConeEdge p u δ v w ∨ ConeEdge p u δ w v
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by
    intro v
    rintro (h | h) <;> exact h.1 rfl⟩

/-- An incoming and outgoing segment in the same cone force a large angle. -/
theorem angle_lower_bound_of_two_cone_edges {a b c u : Point} {δ : ℝ}
    (hin : InnerProductGeometry.angle (b - a) u ≤ δ)
    (hout : InnerProductGeometry.angle (c - b) u ≤ δ) :
    Real.pi - 2 * δ ≤ EuclideanGeometry.angle a b c := by
  have ht := InnerProductGeometry.angle_le_angle_add_angle (b - a) u (c - b)
  rw [InnerProductGeometry.angle_comm u (c - b)] at ht
  change Real.pi - 2 * δ ≤ InnerProductGeometry.angle (a - b) (c - b)
  rw [show a - b = -(b - a) by abel, InnerProductGeometry.angle_neg_left]
  linarith

/-- Under the angle bound, there is no directed path of length two in one cone. -/
theorem not_two_cone_edges {V : Type*} {p : V → Point} {u : Point} {δ : ℝ}
    (hp : Function.Injective p) (hδ : δ < Real.pi / 2)
    (hangle : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      EuclideanGeometry.angle (p a) (p b) (p c) < Real.pi - 2 * δ)
    {a b c : V} (hin : ConeEdge p u δ a b) (hout : ConeEdge p u δ b c) : False := by
  have hlarge := angle_lower_bound_of_two_cone_edges hin.2 hout.2
  by_cases hac : a = c
  · subst c
    rw [EuclideanGeometry.angle_self_of_ne (fun h => hin.1 (hp h))] at hlarge
    linarith
  · exact (not_lt_of_ge hlarge) (hangle a b c hin.1 hac hout.1)

/-- Sources and sinks in a narrow direction cone form its two colour classes. -/
theorem coneGraph_colorable {V : Type*} {p : V → Point} {u : Point} {δ : ℝ}
    (hp : Function.Injective p) (hδ : δ < Real.pi / 2)
    (hangle : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      EuclideanGeometry.angle (p a) (p b) (p c) < Real.pi - 2 * δ) :
    (coneGraph p u δ).Colorable 2 := by
  classical
  let color (v : V) : Fin 2 := if ∃ w, ConeEdge p u δ v w then 0 else 1
  have hvalid {a b : V} (hab : ConeEdge p u δ a b) : color a ≠ color b := by
    have ha : ∃ w, ConeEdge p u δ a w := ⟨b, hab⟩
    have hb : ¬ ∃ w, ConeEdge p u δ b w := by
      rintro ⟨c, hbc⟩
      exact not_two_cone_edges hp hδ hangle hab hbc
    simp [color, ha, hb]
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro v w h
  rcases h with h | h
  · exact hvalid h
  · exact (hvalid h).symm

/-- `k` cone classes covering all segments give the usual `2^k` size bound. -/
theorem card_le_two_pow_of_cone_cover
    {V : Type*} [Fintype V] {p : V → Point} (hp : Function.Injective p)
    (k : ℕ) (u : Fin k → Point) (δ : ℝ) (hδ : δ < Real.pi / 2)
    (hangle : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      EuclideanGeometry.angle (p a) (p b) (p c) < Real.pi - 2 * δ)
    (cover : ∀ v w, v ≠ w →
      ∃ i, ConeEdge p (u i) δ v w ∨ ConeEdge p (u i) δ w v) :
    Fintype.card V ≤ 2 ^ k := by
  exact card_le_two_pow_of_bipartite_cover k (fun i => coneGraph p (u i) δ)
    (fun _ => coneGraph_colorable hp hδ hangle) cover

/-- The weighted version also records which direction classes miss each vertex. -/
theorem cone_cover_weighted_bound
    {V : Type*} [Fintype V] {p : V → Point} (hp : Function.Injective p)
    (k : ℕ) (u : Fin k → Point) (δ : ℝ) (hδ : δ < Real.pi / 2)
    (hangle : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      EuclideanGeometry.angle (p a) (p b) (p c) < Real.pi - 2 * δ)
    (cover : ∀ v w, v ≠ w →
      ∃ i, ConeEdge p (u i) δ v w ∨ ConeEdge p (u i) δ w v) :
    ∑ v, 2 ^ (k - (activeParts (fun i => coneGraph p (u i) δ) v).card) ≤ 2 ^ k := by
  exact bipartite_cover_weighted_bound k (fun i => coneGraph p (u i) δ)
    (fun _ => coneGraph_colorable hp hδ hangle) cover

/-- A cover of vector directions restricts to every finite point configuration. -/
theorem finset_card_le_two_pow_of_direction_cover
    (s : Finset Point) (k : ℕ) (u : Fin k → Point) (δ : ℝ)
    (hδ : δ < Real.pi / 2)
    (hangle : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a ≠ b → a ≠ c → b ≠ c →
      EuclideanGeometry.angle a b c < Real.pi - 2 * δ)
    (cover : ∀ x : Point, x ≠ 0 → ∃ i,
      InnerProductGeometry.angle x (u i) ≤ δ ∨
      InnerProductGeometry.angle (-x) (u i) ≤ δ) :
    s.card ≤ 2 ^ k := by
  classical
  have hcard := card_le_two_pow_of_cone_cover
    (p := fun v : s => v.val) Subtype.val_injective k u δ hδ ?_ ?_
  · simpa only [Fintype.card_coe] using hcard
  · intro a b c hab hac hbc
    exact hangle a.val a.property b.val b.property c.val c.property
      (fun h => hab (Subtype.ext h)) (fun h => hac (Subtype.ext h))
      (fun h => hbc (Subtype.ext h))
  · intro v w hvw
    have hne : w.val - v.val ≠ 0 := by
      intro h
      exact hvw (Subtype.ext (sub_eq_zero.mp h).symm)
    obtain ⟨i, hi | hi⟩ := cover (w.val - v.val) hne
    · exact ⟨i, Or.inl ⟨hvw, hi⟩⟩
    · exact ⟨i, Or.inr ⟨hvw.symm, by simpa only [neg_sub] using hi⟩⟩

/-- A directional cover forces a large angle as soon as there are more than `2^k` points. -/
theorem hasLargeAngle_of_direction_cover
    (s : Finset Point) (k : ℕ) (u : Fin k → Point) (δ : ℝ)
    (hδ : δ < Real.pi / 2) (hcard : 2 ^ k < s.card)
    (cover : ∀ x : Point, x ≠ 0 → ∃ i,
      InnerProductGeometry.angle x (u i) ≤ δ ∨
      InnerProductGeometry.angle (-x) (u i) ≤ δ) :
    HasLargeAngle s (Real.pi - 2 * δ) := by
  by_contra h
  have hangle : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a ≠ b → a ≠ c → b ≠ c →
      EuclideanGeometry.angle a b c < Real.pi - 2 * δ := by
    intro a ha b hb c hc hab hac hbc
    apply lt_of_not_ge
    intro hle
    exact h ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hle⟩
  exact (not_le_of_gt hcard)
    (finset_card_le_two_pow_of_direction_cover s k u δ hδ hangle cover)

theorem guaranteed_of_direction_cover
    (n k : ℕ) (u : Fin k → Point) (δ : ℝ)
    (hδ : δ < Real.pi / 2) (hn : 2 ^ k < n)
    (cover : ∀ x : Point, x ≠ 0 → ∃ i,
      InnerProductGeometry.angle x (u i) ≤ δ ∨
      InnerProductGeometry.angle (-x) (u i) ≤ δ) :
    Guaranteed n (Real.pi - 2 * δ) := by
  intro s hs
  exact hasLargeAngle_of_direction_cover s k u δ hδ (hs ▸ hn) cover

end JSP404
