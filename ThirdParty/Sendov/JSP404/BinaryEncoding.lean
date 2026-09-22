import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Tactic

/-!
# Binary encodings for partitions of complete graphs

This is the finite combinatorial counting argument behind the even-partition
lemmas of Erdős and Szekeres (1960), §3.  It makes no geometric assumptions.
Vertices with unspecified coordinates are encoded by disjoint Boolean subcubes.
-/

namespace JSP404

open scoped BigOperators

/-- A pairwise separating collection of partially specified Boolean words occupies
at most the full Boolean cube.  Unspecified coordinates contribute a factor of two.
-/
theorem sum_free_binary_coordinates_le
    {V : Type*} [Fintype V] (k : ℕ)
    (specified : V → Finset (Fin k)) (bit : V → Fin k → Bool)
    (separates : ∀ v w, v ≠ w → ∃ i,
      i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i) :
    ∑ v, 2 ^ (k - (specified v).card) ≤ 2 ^ k := by
  classical
  let encode : (Σ v, ({i : Fin k // i ∉ specified v} → Bool)) → (Fin k → Bool) :=
    fun p i => if h : i ∈ specified p.1 then bit p.1 i else p.2 ⟨i, h⟩
  have hinj : Function.Injective encode := by
    rintro ⟨v, f⟩ ⟨w, g⟩ h
    have hvw : v = w := by
      by_contra hne
      obtain ⟨i, hv, hw, hbits⟩ := separates v w hne
      have hi := congrFun h i
      exact hbits (by simpa [encode, hv, hw] using hi)
    subst w
    have hfg : f = g := by
      funext i
      have hi := congrFun h i.val
      simpa [encode, i.property] using hi
    subst g
    rfl
  have hcard := Fintype.card_le_of_injective encode hinj
  simpa [Fintype.card_sigma, Fintype.card_fun, Fintype.card_subtype_compl] using hcard

/-- In particular, a separating binary encoding in k coordinates has at most 2^k
vertices.  Choosing a bipartition for each part of an even edge partition supplies
such an encoding.
-/
theorem card_le_two_pow_of_binary_separation
    {V : Type*} [Fintype V] (k : ℕ) (bit : V → Fin k → Bool)
    (separates : ∀ v w, v ≠ w → ∃ i, bit v i ≠ bit w i) :
    Fintype.card V ≤ 2 ^ k := by
  classical
  have hinj : Function.Injective bit := by
    intro v w h
    by_contra hne
    obtain ⟨i, hi⟩ := separates v w hne
    exact hi (congrFun h i)
  simpa using Fintype.card_le_of_injective bit hinj

/-- Coordinates in which a vertex has an incident edge. -/
noncomputable def activeParts {V : Type*} {k : ℕ}
    (G : Fin k → SimpleGraph V) (v : V) : Finset (Fin k) :=
  @Finset.filter _ (fun i => ∃ w, (G i).Adj v w) (Classical.decPred _) Finset.univ

/-- The weighted even-partition bound, allowing overlapping parts as well as
partitions.  Each graph need only have a two-colouring; every pair must be covered.
-/
theorem bipartite_cover_weighted_bound
    {V : Type*} [Fintype V] (k : ℕ) (G : Fin k → SimpleGraph V)
    (hc : ∀ i, (G i).Colorable 2)
    (cover : ∀ v w, v ≠ w → ∃ i, (G i).Adj v w) :
    ∑ v, 2 ^ (k - (activeParts G v).card) ≤ 2 ^ k := by
  classical
  let color (i : Fin k) : (G i).Coloring (Fin 2) := Classical.choice (hc i)
  let bit (v : V) (i : Fin k) : Bool := finTwoEquiv (color i v)
  apply sum_free_binary_coordinates_le k (activeParts G) bit
  intro v w hne
  obtain ⟨i, hi⟩ := cover v w hne
  refine ⟨i, ?_, ?_, ?_⟩
  · simp only [activeParts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hi⟩
  · simp only [activeParts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, hi.symm⟩
  · intro h
    exact (color i).valid hi (finTwoEquiv.injective h)

/-- A cover of a complete graph by k bipartite graphs has at most 2^k vertices. -/
theorem card_le_two_pow_of_bipartite_cover
    {V : Type*} [Fintype V] (k : ℕ) (G : Fin k → SimpleGraph V)
    (hc : ∀ i, (G i).Colorable 2)
    (cover : ∀ v w, v ≠ w → ∃ i, (G i).Adj v w) :
    Fintype.card V ≤ 2 ^ k := by
  classical
  let color (i : Fin k) : (G i).Coloring (Fin 2) := Classical.choice (hc i)
  apply card_le_two_pow_of_binary_separation k (fun v i => finTwoEquiv (color i v))
  intro v w hne
  obtain ⟨i, hi⟩ := cover v w hne
  exact ⟨i, fun h => (color i).valid hi (finTwoEquiv.injective h)⟩

end JSP404
