import Jsp000404.IntervalPacking

/-!
# Integer-shift transport of the genuine interval floor sum

Integer floor, rather than truncated natural floor, telescopes without any
sign condition on individual gaps. The nonnegative-gap adapter then recovers
`linearFloorSum 1` on actual ordered rows. No coordinate-compression map or
support-invariance hypothesis is hidden in the transport identity.
-/

namespace Jsp404

/-- Signed floor sum of all consecutive interval gaps, including the final
gap to `right`. Taking `right = left + π/λ` includes the cyclic wrap. -/
noncomputable def intLinearFloorSum (left right : ℝ) : List ℝ → ℤ
  | [] => ⌊right - left⌋
  | x :: xs => ⌊x - left⌋ + intLinearFloorSum x right xs

/-- Attach an arbitrary integer shift to every internal coordinate. All
internal shifts cancel, leaving only the endpoint shift difference. -/
theorem intLinearFloorSum_integer_transport
    (left right : ℝ) (sl sr : ℤ) (xs : List (ℝ × ℤ)) :
    intLinearFloorSum (left + (sl : ℝ)) (right + (sr : ℝ))
        (xs.map fun x => x.1 + (x.2 : ℝ)) =
      intLinearFloorSum left right (xs.map Prod.fst) + sr - sl := by
  induction xs generalizing left sl with
  | nil =>
    simp only [List.map_nil, intLinearFloorSum]
    have hgap : right + (sr : ℝ) - (left + (sl : ℝ)) =
        (right - left) + ((sr - sl : ℤ) : ℝ) := by push_cast; ring
    rw [hgap, Int.floor_add_intCast]
    omega
  | cons x xs ih =>
    simp only [List.map_cons, intLinearFloorSum]
    rw [ih x.1 x.2]
    have hgap : x.1 + (x.2 : ℝ) - (left + (sl : ℝ)) =
        (x.1 - left) + ((x.2 - sl : ℤ) : ℝ) := by push_cast; ring
    rw [hgap, Int.floor_add_intCast]
    omega

/-- On a sorted interval row, all primitive gaps are nonnegative, so the
signed floor sum is exactly the existing natural floor sum at unit scale. -/
theorem intLinearFloorSum_eq_nat (left right : ℝ) (xs : List ℝ)
    (hs : xs.Pairwise (· ≤ ·))
    (hmem : ∀ x ∈ xs, left ≤ x ∧ x ≤ right) (hlr : left ≤ right) :
    intLinearFloorSum left right xs = (linearFloorSum 1 left right xs : ℤ) := by
  induction xs generalizing left with
  | nil =>
    simp only [intLinearFloorSum, linearFloorSum, div_one]
    exact (Int.natCast_floor_eq_floor (sub_nonneg.mpr hlr)).symm
  | cons x xs ih =>
    have hlx := (hmem x List.mem_cons_self).1
    have hxr := (hmem x List.mem_cons_self).2
    have htl : xs.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hs).2
    have hmem' : ∀ y ∈ xs, x ≤ y ∧ y ≤ right := by
      intro y hy
      exact ⟨(List.pairwise_cons.mp hs).1 y hy,
        (hmem y (List.mem_cons_of_mem x hy)).2⟩
    simp only [intLinearFloorSum, linearFloorSum, div_one, Nat.cast_add]
    rw [ih x htl hmem' hxr,
      Int.natCast_floor_eq_floor (sub_nonneg.mpr hlx)]

/-- Natural floor transport when both the old and shifted row are ordered
inside their respective endpoint windows. -/
theorem linearFloorSum_integer_transport
    (left right : ℝ) (sl sr : ℤ) (xs : List (ℝ × ℤ))
    (hs : (xs.map Prod.fst).Pairwise (· ≤ ·))
    (hmem : ∀ x ∈ xs.map Prod.fst, left ≤ x ∧ x ≤ right)
    (hlr : left ≤ right)
    (hs' : (xs.map fun x => x.1 + (x.2 : ℝ)).Pairwise (· ≤ ·))
    (hmem' : ∀ x ∈ xs.map (fun x => x.1 + (x.2 : ℝ)),
      left + (sl : ℝ) ≤ x ∧ x ≤ right + (sr : ℝ))
    (hlr' : left + (sl : ℝ) ≤ right + (sr : ℝ)) :
    (linearFloorSum 1 (left + (sl : ℝ)) (right + (sr : ℝ))
        (xs.map fun x => x.1 + (x.2 : ℝ)) : ℤ) =
      (linearFloorSum 1 left right (xs.map Prod.fst) : ℤ) + sr - sl := by
  rw [← intLinearFloorSum_eq_nat _ _ _ hs' hmem' hlr',
    ← intLinearFloorSum_eq_nat _ _ _ hs hmem hlr]
  exact intLinearFloorSum_integer_transport left right sl sr xs

/-- Strip transport with the same fractional width `δ`. The exact natural
identity is `newCells + n = oldCells + n'`. -/
theorem linearFloorSum_strip_transport (δ : ℝ) (n n' : ℕ)
    (xs : List (ℝ × ℤ))
    (hs : (xs.map Prod.fst).Pairwise (· ≤ ·))
    (hmem : ∀ x ∈ xs.map Prod.fst, 0 ≤ x ∧ x ≤ (n : ℝ) + δ)
    (hwidth : 0 ≤ (n : ℝ) + δ)
    (hs' : (xs.map fun x => x.1 + (x.2 : ℝ)).Pairwise (· ≤ ·))
    (hmem' : ∀ x ∈ xs.map (fun x => x.1 + (x.2 : ℝ)),
      0 ≤ x ∧ x ≤ (n' : ℝ) + δ)
    (hwidth' : 0 ≤ (n' : ℝ) + δ) :
    linearFloorSum 1 0 ((n' : ℝ) + δ)
        (xs.map fun x => x.1 + (x.2 : ℝ)) + n =
      linearFloorSum 1 0 ((n : ℝ) + δ) (xs.map Prod.fst) + n' := by
  have hend : (n : ℝ) + δ + (((n' : ℤ) - (n : ℤ) : ℤ) : ℝ) =
      (n' : ℝ) + δ := by push_cast; ring
  have hmem'' : ∀ x ∈ xs.map (fun x => x.1 + (x.2 : ℝ)),
      (0 : ℝ) + ((0 : ℤ) : ℝ) ≤ x ∧
      x ≤ (n : ℝ) + δ + (((n' : ℤ) - (n : ℤ) : ℤ) : ℝ) := by
    simpa only [Int.cast_zero, add_zero, hend] using hmem'
  have hwidth'' : (0 : ℝ) + ((0 : ℤ) : ℝ) ≤
      (n : ℝ) + δ + (((n' : ℤ) - (n : ℤ) : ℤ) : ℝ) := by
    simpa only [Int.cast_zero, add_zero, hend] using hwidth'
  have h := linearFloorSum_integer_transport 0 ((n : ℝ) + δ)
    0 ((n' : ℤ) - (n : ℤ)) xs hs hmem hwidth hs' hmem'' hwidth''
  simp only [Int.cast_zero, add_zero, hend, sub_zero] at h
  have hc : (linearFloorSum 1 0 ((n' : ℝ) + δ)
      (xs.map fun x => x.1 + (x.2 : ℝ)) : ℤ) + (n : ℤ) =
      (linearFloorSum 1 0 ((n : ℝ) + δ) (xs.map Prod.fst) : ℤ) + (n' : ℤ) := by
    omega
  exact_mod_cast hc

#print axioms intLinearFloorSum_integer_transport
#print axioms intLinearFloorSum_eq_nat
#print axioms linearFloorSum_integer_transport
#print axioms linearFloorSum_strip_transport

end Jsp404
