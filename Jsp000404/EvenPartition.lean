import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Fintype.Basic

/-!
# Erdős–Szekeres even-partition lemma (Sendov Lemma 3.1)

If all distinct-vertex pairs of an `N`-element type are covered by the edges of
`n` two-colorable simple graphs, then `N ≤ 2 ^ n`. Equivalently: if the edges
of `K_N` are partitioned into `n` subgraphs each containing no odd closed walk,
then `N ≤ 2 ^ n`.

This is the combinatorial engine of Sendov's minimax-angle theorem.
-/

open SimpleGraph Finset

namespace Jsp404

/-- A covering of all distinct-vertex pairs by `n` two-colorable simple graphs. -/
structure EvenCover (V : Type*) [DecidableEq V] [Fintype V] (n : ℕ) where
  G : Fin n → SimpleGraph V
  dec : ∀ i, DecidableRel (G i).Adj
  cover : ∀ v w : V, v ≠ w → ∃ i, (G i).Adj v w
  colorable : ∀ i, (G i).Colorable 2

attribute [instance] EvenCover.dec

/-- Restrict an even cover of `n + 1` graphs to a subset `s` on which `G 0`
has no edges: the remaining `n` graphs still cover `s`. -/
def EvenCover.restrict {V : Type*} [DecidableEq V] [Fintype V] {n : ℕ}
    (C : EvenCover V (n + 1)) (s : Finset V)
    (h0 : ∀ v w : s, ¬ (C.G 0).Adj v w) : EvenCover s n where
  G i := (C.G i.succ).induce s
  dec i := fun v w => C.dec _ v.1 w.1
  cover v w hvw := by
    obtain ⟨i, hi⟩ := C.cover v.1 w.1 (Subtype.coe_injective.ne hvw)
    have hi0 : i ≠ 0 := fun h => h0 v w (h ▸ hi)
    have hi1 : 1 ≤ i.1 := by
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · exact absurd rfl hi0
      · exact Nat.one_le_of_lt (Fin.succ_pos _)
    refine ⟨⟨i.1 - 1, by have := i.2; omega⟩, ?_⟩
    have hs : Fin.succ ⟨i.1 - 1, by have := i.2; omega⟩ = i := by
      ext; simp [Fin.succ]; omega
    show ((C.G (Fin.succ ⟨i.1 - 1, _⟩)).induce s).Adj v w
    rw [hs]
    exact hi
  colorable i := by
    obtain ⟨C0⟩ := C.colorable i.succ
    refine ⟨fun v => C0 v.1, ?_⟩
    intro v w hvw
    exact C0.valid hvw

/-- If a graph has no closed walk of odd length, it is 2-colorable:
color each vertex by the parity of its distance to a component root.
(Mathlib lists "bipartite iff no odd cycle" as a TODO; we prove the
direction needed here via distance parity.) -/
theorem colorable_two_of_no_odd_closed_walk {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : ∀ {v : V} (w : G.Walk v v), Odd w.length → False) : G.Colorable 2 := by
  classical
  -- canonical root of each connected component
  set root : V → V := fun v => (G.connectedComponentMk v).out with hroot
  have reach_self : ∀ u : V, G.Reachable (root u) u := by
    intro u
    apply ConnectedComponent.exact
    show G.connectedComponentMk (root u) = G.connectedComponentMk u
    rw [hroot]
    exact (G.connectedComponentMk u).out_eq
  have reach : ∀ u v : V, G.Adj u v → G.Reachable (root u) v := by
    intro u v huv
    apply ConnectedComponent.exact
    show G.connectedComponentMk (root u) = G.connectedComponentMk v
    rw [hroot]
    exact (G.connectedComponentMk u).out_eq.trans
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj huv)
  have root_eq : ∀ u v : V, G.Adj u v → root u = root v := by
    intro u v huv
    have h2 := ConnectedComponent.connectedComponentMk_eq_of_adj huv
    simp only [hroot, h2]
  refine ⟨fun v => ⟨G.dist (root v) v % 2, by omega⟩, ?_⟩
  intro u v huv
  rw [SimpleGraph.top_adj]
  intro hpar
  have hpar' : G.dist (root u) u % 2 = G.dist (root v) v % 2 :=
    congrArg Fin.val hpar
  rw [← root_eq u v huv] at hpar'
  -- distances to the common root differ by at most one
  have huv_r : G.Reachable u v := ⟨Walk.cons huv Walk.nil⟩
  have h1 : G.dist (root u) u ≤ G.dist (root u) v + G.dist v u :=
    (reach u v huv).dist_triangle_left u
  have h2 : G.dist (root u) v ≤ G.dist (root u) u + G.dist u v :=
    huv_r.dist_triangle_right (root u)
  have hdist1 : G.dist u v = 1 := by
    simp [SimpleGraph.dist, edist_eq_one_iff_adj.mpr huv]
  have hdv : G.dist v u = G.dist u v := SimpleGraph.dist_comm
  rw [hdv, hdist1] at h1
  rw [hdist1] at h2
  have hdeq : G.dist (root u) u = G.dist (root u) v := by omega
  -- assemble the odd closed walk r → u → v → r
  obtain ⟨w₁, hw₁⟩ := (reach_self u).exists_walk_length_eq_dist
  obtain ⟨w₂, hw₂⟩ := (reach u v huv).exists_walk_length_eq_dist
  have hW : ((w₁.concat huv).append w₂.reverse).length =
      G.dist (root u) u + 1 + G.dist (root u) v := by
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_concat,
      SimpleGraph.Walk.length_reverse, hw₁, hw₂]
  exact h _ ⟨G.dist (root u) u, by rw [hW]; omega⟩

/-- **Erdős–Szekeres even-partition lemma.** If every pair of distinct vertices
is covered by one of `n` two-colorable graphs, then `|V| ≤ 2 ^ n`. -/
theorem card_le_two_pow_of_evenCover {V : Type*} [DecidableEq V] [Fintype V]
    {n : ℕ} (C : EvenCover V n) : Fintype.card V ≤ 2 ^ n := by
  induction n generalizing V with
  | zero =>
    by_contra hlt
    push Not at hlt
    obtain ⟨v, w, hvw⟩ := Fintype.exists_pair_of_one_lt_card hlt
    obtain ⟨i, -⟩ := C.cover v w hvw
    exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨C0⟩ := C.colorable 0
    classical
    set A : Finset V := Finset.univ.filter fun v => C0 v = 0 with hA
    set B : Finset V := Finset.univ.filter fun v => C0 v = 1 with hB
    have hAB : ∀ x : V, C0 x = 0 ∨ C0 x = 1 := fun x => by
      rcases C0 x with ⟨_|_|v, hv⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega
    have hunion : A ∪ B = Finset.univ := by
      ext x; simp [hA, hB, hAB x]
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro x hxA hxB
      have h1 : C0 x = 0 := (Finset.mem_filter.mp hxA).2
      have h2 : C0 x = 1 := (Finset.mem_filter.mp hxB).2
      rw [h1] at h2
      exact absurd h2 (by decide)
    have noedge0 : ∀ v w : A, ¬ (C.G 0).Adj v w := by
      intro v w hadj
      have hv : C0 v.1 = 0 := (Finset.mem_filter.mp v.2).2
      have hw : C0 w.1 = 0 := (Finset.mem_filter.mp w.2).2
      exact absurd (hv.trans hw.symm) (C0.valid hadj)
    have noedge0' : ∀ v w : B, ¬ (C.G 0).Adj v w := by
      intro v w hadj
      have hv : C0 v.1 = 1 := (Finset.mem_filter.mp v.2).2
      have hw : C0 w.1 = 1 := (Finset.mem_filter.mp w.2).2
      exact absurd (hv.trans hw.symm) (C0.valid hadj)
    have hA' := ih (C.restrict A noedge0)
    have hB' := ih (C.restrict B noedge0')
    rw [Fintype.card_coe] at hA' hB'
    have hcard : Fintype.card V = A.card + B.card := by
      rw [← Finset.card_univ, ← hunion, Finset.card_union_of_disjoint hdisj]
    omega

end Jsp404
