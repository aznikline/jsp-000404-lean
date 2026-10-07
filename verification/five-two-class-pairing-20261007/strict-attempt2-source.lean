import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

set_option autoImplicit false

/-! Pure five-point pairing incidence. This file does not construct any
actual geometric classes. It is SOURCE_ONLY until separately checked.
-/

open scoped BigOperators

namespace Jsp404.FiveTwoClassPairing

private def sameIndicator (code : Fin 5 → Fin 5 → Bool) (p i j : Fin 5) : ℕ :=
  if i ≠ p ∧ j ≠ p ∧ j ≠ i ∧ code p j = code p i then 1 else 0

private def distinctIndicator (p i j : Fin 5) : ℕ :=
  if p ≠ i ∧ p ≠ j ∧ i ≠ j then 1 else 0

private def triangleIndicator (code : Fin 5 → Fin 5 → Bool) (p i j : Fin 5) : ℕ :=
  sameIndicator code p i j + sameIndicator code i p j + sameIndicator code j p i

private theorem partners_count (code : Fin 5 → Fin 5 → Bool)
    (hcard : ∀ p b, ((Finset.univ.erase p).filter (fun i => code p i = b)).card = 2)
    (p i : Fin 5) :
    (∑ j : Fin 5, sameIndicator code p i j) = if i ≠ p then 1 else 0 := by
  classical
  by_cases hi : i ≠ p
  · rw [ite_eq_left hi]
    let F := (Finset.univ.erase p).filter (fun j => code p j = code p i)
    have hF : F.card = 2 := hcard p (code p i)
    have himem : i ∈ F := by simp [F, hi]
    have hset : Finset.univ.filter (fun j : Fin 5 =>
        i ≠ p ∧ j ≠ p ∧ j ≠ i ∧ code p j = code p i) = F.erase i := by
      ext j
      simp [F, hi, and_assoc, and_left_comm, and_comm]
    calc
      (∑ j : Fin 5, sameIndicator code p i j) =
          (Finset.univ.filter (fun j : Fin 5 =>
            i ≠ p ∧ j ≠ p ∧ j ≠ i ∧ code p j = code p i)).card := by
        simpa only [sameIndicator] using (Finset.card_filter
          (fun j : Fin 5 => i ≠ p ∧ j ≠ p ∧ j ≠ i ∧ code p j = code p i)
          Finset.univ).symm
      _ = (F.erase i).card := congrArg Finset.card hset
      _ = 1 := by simp [Finset.card_erase_of_mem himem, hF]
  · have hip : i = p := not_ne_iff.mp hi
    subst i
    simp [sameIndicator]

private theorem row_count (code : Fin 5 → Fin 5 → Bool)
    (hcard : ∀ p b, ((Finset.univ.erase p).filter (fun i => code p i = b)).card = 2)
    (p : Fin 5) : (∑ i : Fin 5, ∑ j : Fin 5, sameIndicator code p i j) = 4 := by
  classical
  have hset : Finset.univ.filter (fun i : Fin 5 => i ≠ p) = Finset.univ.erase p := by
    ext i
    simp
  calc
    (∑ i : Fin 5, ∑ j : Fin 5, sameIndicator code p i j) =
        ∑ i : Fin 5, if i ≠ p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact partners_count code hcard p i
    _ = (Finset.univ.filter (fun i : Fin 5 => i ≠ p)).card :=
      (Finset.card_filter (fun i : Fin 5 => i ≠ p) Finset.univ).symm
    _ = 4 := by rw [hset]; simp

private theorem same_total (code : Fin 5 → Fin 5 → Bool)
    (hcard : ∀ p b, ((Finset.univ.erase p).filter (fun i => code p i = b)).card = 2) :
    (∑ p : Fin 5, ∑ i : Fin 5, ∑ j : Fin 5, sameIndicator code p i j) = 20 := by
  calc
    (∑ p : Fin 5, ∑ i : Fin 5, ∑ j : Fin 5, sameIndicator code p i j) =
        ∑ _p : Fin 5, (4 : ℕ) := by
      apply Finset.sum_congr rfl
      intro p _
      exact row_count code hcard p
    _ = 20 := by decide

private theorem distinct_total :
    (∑ p : Fin 5, ∑ i : Fin 5, ∑ j : Fin 5, distinctIndicator p i j) = 60 := by
  decide

private theorem triangle_total (code : Fin 5 → Fin 5 → Bool)
    (hcard : ∀ p b, ((Finset.univ.erase p).filter (fun i => code p i = b)).card = 2) :
    (∑ p : Fin 5, ∑ i : Fin 5, ∑ j : Fin 5, triangleIndicator code p i j) = 60 := by
  have htotal := same_total code hcard
  have hsecond : (∑ p : Fin 5, ∑ i : Fin 5, ∑ j : Fin 5,
      sameIndicator code i p j) = 20 := by
    calc
      _ = ∑ i : Fin 5, ∑ p : Fin 5, ∑ j : Fin 5, sameIndicator code i p j :=
        Finset.sum_comm
      _ = 20 := htotal
  have hthird : (∑ p : Fin 5, ∑ i : Fin 5, ∑ j : Fin 5,
      sameIndicator code j p i) = 20 := by
    calc
      _ = ∑ p : Fin 5, ∑ j : Fin 5, ∑ i : Fin 5, sameIndicator code j p i := by
        apply Finset.sum_congr rfl
        intro p _
        exact Finset.sum_comm
      _ = ∑ j : Fin 5, ∑ p : Fin 5, ∑ i : Fin 5, sameIndicator code j p i :=
        Finset.sum_comm
      _ = 20 := htotal
  simp only [triangleIndicator, Finset.sum_add_distrib]
  rw [htotal, hsecond, hthird]

private theorem triangle_exact (code : Fin 5 → Fin 5 → Bool)
    (hcard : ∀ p b, ((Finset.univ.erase p).filter (fun i => code p i = b)).card = 2)
    (htriangle : ∀ p i j, p ≠ i → p ≠ j → i ≠ j →
      code p i = code p j ∨ code i p = code i j ∨ code j p = code j i)
    (p i j : Fin 5) (hpi : p ≠ i) (hpj : p ≠ j) (hij : i ≠ j) :
    triangleIndicator code p i j = 1 := by
  have hle (a b d : Fin 5) : distinctIndicator a b d ≤ triangleIndicator code a b d := by
    by_cases hdist : a ≠ b ∧ a ≠ d ∧ b ≠ d
    · rw [distinctIndicator, ite_eq_left hdist]
      dsimp only [triangleIndicator]
      rcases htriangle a b d hdist.1 hdist.2.1 hdist.2.2 with h | h | h
      · have hs : sameIndicator code a b d = 1 := by
          simp [sameIndicator, hdist.1.symm, hdist.2.1.symm, hdist.2.2.symm, h.symm]
        omega
      · have hs : sameIndicator code b a d = 1 := by
          simp [sameIndicator, hdist.1, hdist.2.2.symm, hdist.2.1.symm, h.symm]
        omega
      · have hs : sameIndicator code d a b = 1 := by
          simp [sameIndicator, hdist.2.1, hdist.2.2, hdist.1.symm, h.symm]
        omega
    · simp only [distinctIndicator, ite_eq_right hdist]
      exact Nat.zero_le _
  have hsum : (∑ a : Fin 5, ∑ b : Fin 5, ∑ d : Fin 5, distinctIndicator a b d) =
      ∑ a : Fin 5, ∑ b : Fin 5, ∑ d : Fin 5, triangleIndicator code a b d := by
    rw [distinct_total, triangle_total code hcard]
  have hrow := (Finset.sum_eq_sum_iff_of_le (fun a _ =>
    Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun d _ => hle a b d)))).mp
      hsum p (Finset.mem_univ p)
  have hpair := (Finset.sum_eq_sum_iff_of_le (fun b _ =>
    Finset.sum_le_sum (fun d _ => hle p b d))).mp hrow i (Finset.mem_univ i)
  have hentry := (Finset.sum_eq_sum_iff_of_le (fun d _ => hle p i d)).mp
    hpair j (Finset.mem_univ j)
  simpa only [distinctIndicator, hpi, hpj, hij, ne_eq, not_false_eq_true, and_self, ite_true] using hentry.symm

/-- In five balanced two-class rows, triangle coverage is automatically
exact: if p pairs i with j, neither other observer pairs the remaining
two. This is solely a combinatorial lemma about the supplied Bool code. -/
theorem same_forces_other_two_different (code : Fin 5 → Fin 5 → Bool)
    (hcard : ∀ p b, ((Finset.univ.erase p).filter (fun i => code p i = b)).card = 2)
    (htriangle : ∀ p i j, p ≠ i → p ≠ j → i ≠ j →
      code p i = code p j ∨ code i p = code i j ∨ code j p = code j i)
    (p i j : Fin 5) (hpi : p ≠ i) (hpj : p ≠ j) (hij : i ≠ j)
    (hsame : code p i = code p j) :
    code i p ≠ code i j ∧ code j p ≠ code j i := by
  have ht := triangle_exact code hcard htriangle p i j hpi hpj hij
  have hpflag : sameIndicator code p i j = 1 := by
    simp [sameIndicator, hpi.symm, hpj.symm, hij.symm, hsame.symm]
  unfold triangleIndicator at ht
  constructor
  · intro hi
    have hiflag : sameIndicator code i p j = 1 := by
      simp [sameIndicator, hpi, hij.symm, hpj.symm, hi.symm]
    omega
  · intro hj
    have hjflag : sameIndicator code j p i = 1 := by
      simp [sameIndicator, hpj, hij, hpi.symm, hj.symm]
    omega

#print axioms same_forces_other_two_different

end Jsp404.FiveTwoClassPairing
