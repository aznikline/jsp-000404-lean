import Jsp000404.GlobalFiveLowStrongModel
import Jsp000404.GlobalFiveLowTerminal0
import Jsp000404.GlobalFiveLowTerminal1
import Jsp000404.GlobalFiveLowTerminal2
import Mathlib.Data.Fin.Rev

/-! Vertex index reversal preserves chord values, all three triangle caps,
and the complete cyclic row budget. Zero projective representatives remain
zero; no reflection of chord values across the period is used. -/

namespace Jsp404.GlobalFiveLowTerminal

private theorem reversed_neighbors_perm (i : Fin 5) :
    (((List.finRange 5).erase i).map Fin.rev).Perm
      ((List.finRange 5).erase i.rev) := by
  have h : ∀ i : Fin 5, (((List.finRange 5).erase i).map Fin.rev).Perm
      ((List.finRange 5).erase i.rev) := by decide
  exact h i

/-- Reverse centre indices without changing the chord values. -/
def reverseModel {n delta : ℝ} {q : Fin 5} (m : FiveModel n delta q) :
    FiveModel n delta q.rev where
  hn := m.hn
  hdelta := m.hdelta
  d i j := m.d i.rev j.rev
  symm i j := m.symm i.rev j.rev
  range i j hij := m.range i.rev j.rev (fun h => hij (Fin.rev_injective h))
  triangle i j k hij hjk := by
    have h := m.triangle k.rev j.rev i.rev
      (Fin.rev_lt_rev.mpr hjk) (Fin.rev_lt_rev.mpr hij)
    rw [m.symm k.rev j.rev, m.symm k.rev i.rev, m.symm j.rev i.rev] at h
    exact h.symm
  budget i hi a b c e hp hab hbc hce := by
    have hi' : i.rev ≠ q := by
      intro h
      apply hi
      have hh := congrArg Fin.rev h
      simpa only [Fin.rev_rev] using hh
    have hp' : [a.rev,b.rev,c.rev,e.rev].Perm ((List.finRange 5).erase i.rev) := by
      simpa only [List.map_cons, List.map_nil] using
        (hp.map Fin.rev).trans (reversed_neighbors_perm i)
    exact m.budget i.rev hi' a.rev b.rev c.rev e.rev hp' hab hbc hce

/-- Four genuine low cyclic budgets are impossible among any five
ordered centres in every LOW strip, with no restriction on the fifth row. -/
theorem model_impossible {n delta : ℝ} {q : Fin 5} (m : FiveModel n delta q) : False := by
  fin_cases q
  · exact model_impossible_0 m
  · exact model_impossible_1 m
  · exact model_impossible_2 m
  · exact model_impossible_1 (reverseModel m)
  · exact model_impossible_0 (reverseModel m)

#print axioms reverseModel
#print axioms model_impossible
end Jsp404.GlobalFiveLowTerminal
