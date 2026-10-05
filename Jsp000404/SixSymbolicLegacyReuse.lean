import Jsp000404.FourRowCertificate

/-! Typed reuse of seven existing forall-strip certificates.
The common profile is explicit; no direction-membership oracle is assumed. -/
set_option pp.fullNames true

namespace Jsp404.SixExactFloorKernel

/-- The existing direction 1 certificate in the common profile. -/
theorem symbolic_mask1_legacy_reuse {n : ℕ} (M : SixModelCompression.ModelSix n)
    (hn4 : 4 ≤ n) (hhigh : (1 / 2 : ℝ) ≤ M.delta)
    (hdef0 : SixModelCompression.rowDefect M 0 = 2)
    (hdef1 : SixModelCompression.rowDefect M 1 = 3)
    (hdef3 : SixModelCompression.rowDefect M 3 = 3)
    (hdef4 : SixModelCompression.rowDefect M 4 = 2)
    (htri012 : M.d 1 2 + 1 ≤ M.d 0 1 ∧ M.d 1 2 < M.d 0 2 ∧ M.d 0 2 < M.d 0 1)
    (htri013 : M.d 0 1 + 1 ≤ M.d 1 3 ∧ M.d 0 1 < M.d 0 3 ∧ M.d 0 3 < M.d 1 3)
    (htri014 : M.d 0 1 + 1 ≤ M.d 1 4 ∧ M.d 0 1 < M.d 0 4 ∧ M.d 0 4 < M.d 1 4)
    (htri023 : M.d 0 2 + 1 ≤ M.d 2 3 ∧ M.d 0 2 < M.d 0 3 ∧ M.d 0 3 < M.d 2 3)
    (htri024 : M.d 0 2 + 1 ≤ M.d 2 4 ∧ M.d 0 2 < M.d 0 4 ∧ M.d 0 4 < M.d 2 4)
    (htri034 : M.d 0 3 + 1 ≤ M.d 3 4 ∧ M.d 0 3 < M.d 0 4 ∧ M.d 0 4 < M.d 3 4)
    (htri123 : M.d 1 2 + 1 ≤ M.d 2 3 ∧ M.d 1 2 < M.d 1 3 ∧ M.d 1 3 < M.d 2 3)
    (htri124 : M.d 1 2 + 1 ≤ M.d 2 4 ∧ M.d 1 2 < M.d 1 4 ∧ M.d 1 4 < M.d 2 4)
    (htri134 : M.d 1 3 + 1 ≤ M.d 3 4 ∧ M.d 1 3 < M.d 1 4 ∧ M.d 1 4 < M.d 3 4)
    (htri234 : M.d 2 3 + 1 ≤ M.d 3 4 ∧ M.d 2 3 < M.d 2 4 ∧ M.d 2 4 < M.d 3 4)
    : False := by
  exact FourRowCertificate.orientation_1_impossible M
    htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
    hdef1

#print axioms symbolic_mask1_legacy_reuse

/-- The existing direction 63 certificate in the common profile. -/
theorem symbolic_mask63_legacy_reuse {n : ℕ} (M : SixModelCompression.ModelSix n)
    (hn4 : 4 ≤ n) (hhigh : (1 / 2 : ℝ) ≤ M.delta)
    (hdef0 : SixModelCompression.rowDefect M 0 = 2)
    (hdef1 : SixModelCompression.rowDefect M 1 = 3)
    (hdef3 : SixModelCompression.rowDefect M 3 = 3)
    (hdef4 : SixModelCompression.rowDefect M 4 = 2)
    (htri012 : M.d 1 2 + 1 ≤ M.d 0 1 ∧ M.d 1 2 < M.d 0 2 ∧ M.d 0 2 < M.d 0 1)
    (htri013 : M.d 1 3 + 1 ≤ M.d 0 1 ∧ M.d 1 3 < M.d 0 3 ∧ M.d 0 3 < M.d 0 1)
    (htri014 : M.d 1 4 + 1 ≤ M.d 0 1 ∧ M.d 1 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 1)
    (htri023 : M.d 2 3 + 1 ≤ M.d 0 2 ∧ M.d 2 3 < M.d 0 3 ∧ M.d 0 3 < M.d 0 2)
    (htri024 : M.d 2 4 + 1 ≤ M.d 0 2 ∧ M.d 2 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 2)
    (htri034 : M.d 3 4 + 1 ≤ M.d 0 3 ∧ M.d 3 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 3)
    (htri123 : M.d 1 2 + 1 ≤ M.d 2 3 ∧ M.d 1 2 < M.d 1 3 ∧ M.d 1 3 < M.d 2 3)
    (htri124 : M.d 1 2 + 1 ≤ M.d 2 4 ∧ M.d 1 2 < M.d 1 4 ∧ M.d 1 4 < M.d 2 4)
    (htri134 : M.d 1 3 + 1 ≤ M.d 3 4 ∧ M.d 1 3 < M.d 1 4 ∧ M.d 1 4 < M.d 3 4)
    (htri234 : M.d 2 3 + 1 ≤ M.d 3 4 ∧ M.d 2 3 < M.d 2 4 ∧ M.d 2 4 < M.d 3 4)
    : False := by
  exact FourRowCertificate.orientation_63_impossible M
    htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
    hdef3

#print axioms symbolic_mask63_legacy_reuse

/-- The existing direction 74 certificate in the common profile. -/
theorem symbolic_mask74_legacy_reuse {n : ℕ} (M : SixModelCompression.ModelSix n)
    (hn4 : 4 ≤ n) (hhigh : (1 / 2 : ℝ) ≤ M.delta)
    (hdef0 : SixModelCompression.rowDefect M 0 = 2)
    (hdef1 : SixModelCompression.rowDefect M 1 = 3)
    (hdef3 : SixModelCompression.rowDefect M 3 = 3)
    (hdef4 : SixModelCompression.rowDefect M 4 = 2)
    (htri012 : M.d 0 1 + 1 ≤ M.d 1 2 ∧ M.d 0 1 < M.d 0 2 ∧ M.d 0 2 < M.d 1 2)
    (htri013 : M.d 1 3 + 1 ≤ M.d 0 1 ∧ M.d 1 3 < M.d 0 3 ∧ M.d 0 3 < M.d 0 1)
    (htri014 : M.d 0 1 + 1 ≤ M.d 1 4 ∧ M.d 0 1 < M.d 0 4 ∧ M.d 0 4 < M.d 1 4)
    (htri023 : M.d 2 3 + 1 ≤ M.d 0 2 ∧ M.d 2 3 < M.d 0 3 ∧ M.d 0 3 < M.d 0 2)
    (htri024 : M.d 0 2 + 1 ≤ M.d 2 4 ∧ M.d 0 2 < M.d 0 4 ∧ M.d 0 4 < M.d 2 4)
    (htri034 : M.d 0 3 + 1 ≤ M.d 3 4 ∧ M.d 0 3 < M.d 0 4 ∧ M.d 0 4 < M.d 3 4)
    (htri123 : M.d 2 3 + 1 ≤ M.d 1 2 ∧ M.d 2 3 < M.d 1 3 ∧ M.d 1 3 < M.d 1 2)
    (htri124 : M.d 1 2 + 1 ≤ M.d 2 4 ∧ M.d 1 2 < M.d 1 4 ∧ M.d 1 4 < M.d 2 4)
    (htri134 : M.d 1 3 + 1 ≤ M.d 3 4 ∧ M.d 1 3 < M.d 1 4 ∧ M.d 1 4 < M.d 3 4)
    (htri234 : M.d 2 3 + 1 ≤ M.d 3 4 ∧ M.d 2 3 < M.d 2 4 ∧ M.d 2 4 < M.d 3 4)
    : False := by
  exact FourRowCertificate.orientation_74_impossible M
    htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
    hdef1

#print axioms symbolic_mask74_legacy_reuse

/-- The existing direction 448 certificate in the common profile. -/
theorem symbolic_mask448_legacy_reuse {n : ℕ} (M : SixModelCompression.ModelSix n)
    (hn4 : 4 ≤ n) (hhigh : (1 / 2 : ℝ) ≤ M.delta)
    (hdef0 : SixModelCompression.rowDefect M 0 = 2)
    (hdef1 : SixModelCompression.rowDefect M 1 = 3)
    (hdef3 : SixModelCompression.rowDefect M 3 = 3)
    (hdef4 : SixModelCompression.rowDefect M 4 = 2)
    (htri012 : M.d 0 1 + 1 ≤ M.d 1 2 ∧ M.d 0 1 < M.d 0 2 ∧ M.d 0 2 < M.d 1 2)
    (htri013 : M.d 0 1 + 1 ≤ M.d 1 3 ∧ M.d 0 1 < M.d 0 3 ∧ M.d 0 3 < M.d 1 3)
    (htri014 : M.d 0 1 + 1 ≤ M.d 1 4 ∧ M.d 0 1 < M.d 0 4 ∧ M.d 0 4 < M.d 1 4)
    (htri023 : M.d 0 2 + 1 ≤ M.d 2 3 ∧ M.d 0 2 < M.d 0 3 ∧ M.d 0 3 < M.d 2 3)
    (htri024 : M.d 0 2 + 1 ≤ M.d 2 4 ∧ M.d 0 2 < M.d 0 4 ∧ M.d 0 4 < M.d 2 4)
    (htri034 : M.d 0 3 + 1 ≤ M.d 3 4 ∧ M.d 0 3 < M.d 0 4 ∧ M.d 0 4 < M.d 3 4)
    (htri123 : M.d 2 3 + 1 ≤ M.d 1 2 ∧ M.d 2 3 < M.d 1 3 ∧ M.d 1 3 < M.d 1 2)
    (htri124 : M.d 2 4 + 1 ≤ M.d 1 2 ∧ M.d 2 4 < M.d 1 4 ∧ M.d 1 4 < M.d 1 2)
    (htri134 : M.d 3 4 + 1 ≤ M.d 1 3 ∧ M.d 3 4 < M.d 1 4 ∧ M.d 1 4 < M.d 1 3)
    (htri234 : M.d 2 3 + 1 ≤ M.d 3 4 ∧ M.d 2 3 < M.d 2 4 ∧ M.d 2 4 < M.d 3 4)
    : False := by
  exact FourRowCertificate.orientation_448_impossible M
    htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
    hdef3

#print axioms symbolic_mask448_legacy_reuse

/-- The existing direction 512 certificate in the common profile. -/
theorem symbolic_mask512_legacy_reuse {n : ℕ} (M : SixModelCompression.ModelSix n)
    (hn4 : 4 ≤ n) (hhigh : (1 / 2 : ℝ) ≤ M.delta)
    (hdef0 : SixModelCompression.rowDefect M 0 = 2)
    (hdef1 : SixModelCompression.rowDefect M 1 = 3)
    (hdef3 : SixModelCompression.rowDefect M 3 = 3)
    (hdef4 : SixModelCompression.rowDefect M 4 = 2)
    (htri012 : M.d 0 1 + 1 ≤ M.d 1 2 ∧ M.d 0 1 < M.d 0 2 ∧ M.d 0 2 < M.d 1 2)
    (htri013 : M.d 0 1 + 1 ≤ M.d 1 3 ∧ M.d 0 1 < M.d 0 3 ∧ M.d 0 3 < M.d 1 3)
    (htri014 : M.d 0 1 + 1 ≤ M.d 1 4 ∧ M.d 0 1 < M.d 0 4 ∧ M.d 0 4 < M.d 1 4)
    (htri023 : M.d 0 2 + 1 ≤ M.d 2 3 ∧ M.d 0 2 < M.d 0 3 ∧ M.d 0 3 < M.d 2 3)
    (htri024 : M.d 0 2 + 1 ≤ M.d 2 4 ∧ M.d 0 2 < M.d 0 4 ∧ M.d 0 4 < M.d 2 4)
    (htri034 : M.d 0 3 + 1 ≤ M.d 3 4 ∧ M.d 0 3 < M.d 0 4 ∧ M.d 0 4 < M.d 3 4)
    (htri123 : M.d 1 2 + 1 ≤ M.d 2 3 ∧ M.d 1 2 < M.d 1 3 ∧ M.d 1 3 < M.d 2 3)
    (htri124 : M.d 1 2 + 1 ≤ M.d 2 4 ∧ M.d 1 2 < M.d 1 4 ∧ M.d 1 4 < M.d 2 4)
    (htri134 : M.d 1 3 + 1 ≤ M.d 3 4 ∧ M.d 1 3 < M.d 1 4 ∧ M.d 1 4 < M.d 3 4)
    (htri234 : M.d 3 4 + 1 ≤ M.d 2 3 ∧ M.d 3 4 < M.d 2 4 ∧ M.d 2 4 < M.d 2 3)
    : False := by
  exact FourRowCertificate.orientation_512_impossible M
    htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
    hdef3

#print axioms symbolic_mask512_legacy_reuse

/-- The existing direction 513 certificate in the common profile. -/
theorem symbolic_mask513_legacy_reuse {n : ℕ} (M : SixModelCompression.ModelSix n)
    (hn4 : 4 ≤ n) (hhigh : (1 / 2 : ℝ) ≤ M.delta)
    (hdef0 : SixModelCompression.rowDefect M 0 = 2)
    (hdef1 : SixModelCompression.rowDefect M 1 = 3)
    (hdef3 : SixModelCompression.rowDefect M 3 = 3)
    (hdef4 : SixModelCompression.rowDefect M 4 = 2)
    (htri012 : M.d 1 2 + 1 ≤ M.d 0 1 ∧ M.d 1 2 < M.d 0 2 ∧ M.d 0 2 < M.d 0 1)
    (htri013 : M.d 0 1 + 1 ≤ M.d 1 3 ∧ M.d 0 1 < M.d 0 3 ∧ M.d 0 3 < M.d 1 3)
    (htri014 : M.d 0 1 + 1 ≤ M.d 1 4 ∧ M.d 0 1 < M.d 0 4 ∧ M.d 0 4 < M.d 1 4)
    (htri023 : M.d 0 2 + 1 ≤ M.d 2 3 ∧ M.d 0 2 < M.d 0 3 ∧ M.d 0 3 < M.d 2 3)
    (htri024 : M.d 0 2 + 1 ≤ M.d 2 4 ∧ M.d 0 2 < M.d 0 4 ∧ M.d 0 4 < M.d 2 4)
    (htri034 : M.d 0 3 + 1 ≤ M.d 3 4 ∧ M.d 0 3 < M.d 0 4 ∧ M.d 0 4 < M.d 3 4)
    (htri123 : M.d 1 2 + 1 ≤ M.d 2 3 ∧ M.d 1 2 < M.d 1 3 ∧ M.d 1 3 < M.d 2 3)
    (htri124 : M.d 1 2 + 1 ≤ M.d 2 4 ∧ M.d 1 2 < M.d 1 4 ∧ M.d 1 4 < M.d 2 4)
    (htri134 : M.d 1 3 + 1 ≤ M.d 3 4 ∧ M.d 1 3 < M.d 1 4 ∧ M.d 1 4 < M.d 3 4)
    (htri234 : M.d 3 4 + 1 ≤ M.d 2 3 ∧ M.d 3 4 < M.d 2 4 ∧ M.d 2 4 < M.d 2 3)
    : False := by
  exact FourRowCertificate.orientation_513_impossible M
    htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
    hdef1

#print axioms symbolic_mask513_legacy_reuse

/-- The existing direction 948 certificate in the common profile. -/
theorem symbolic_mask948_legacy_reuse {n : ℕ} (M : SixModelCompression.ModelSix n)
    (hn4 : 4 ≤ n) (hhigh : (1 / 2 : ℝ) ≤ M.delta)
    (hdef0 : SixModelCompression.rowDefect M 0 = 2)
    (hdef1 : SixModelCompression.rowDefect M 1 = 3)
    (hdef3 : SixModelCompression.rowDefect M 3 = 3)
    (hdef4 : SixModelCompression.rowDefect M 4 = 2)
    (htri012 : M.d 0 1 + 1 ≤ M.d 1 2 ∧ M.d 0 1 < M.d 0 2 ∧ M.d 0 2 < M.d 1 2)
    (htri013 : M.d 0 1 + 1 ≤ M.d 1 3 ∧ M.d 0 1 < M.d 0 3 ∧ M.d 0 3 < M.d 1 3)
    (htri014 : M.d 1 4 + 1 ≤ M.d 0 1 ∧ M.d 1 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 1)
    (htri023 : M.d 0 2 + 1 ≤ M.d 2 3 ∧ M.d 0 2 < M.d 0 3 ∧ M.d 0 3 < M.d 2 3)
    (htri024 : M.d 2 4 + 1 ≤ M.d 0 2 ∧ M.d 2 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 2)
    (htri034 : M.d 3 4 + 1 ≤ M.d 0 3 ∧ M.d 3 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 3)
    (htri123 : M.d 1 2 + 1 ≤ M.d 2 3 ∧ M.d 1 2 < M.d 1 3 ∧ M.d 1 3 < M.d 2 3)
    (htri124 : M.d 2 4 + 1 ≤ M.d 1 2 ∧ M.d 2 4 < M.d 1 4 ∧ M.d 1 4 < M.d 1 2)
    (htri134 : M.d 3 4 + 1 ≤ M.d 1 3 ∧ M.d 3 4 < M.d 1 4 ∧ M.d 1 4 < M.d 1 3)
    (htri234 : M.d 3 4 + 1 ≤ M.d 2 3 ∧ M.d 3 4 < M.d 2 4 ∧ M.d 2 4 < M.d 2 3)
    : False := by
  exact FourRowCertificate.orientation_948_impossible M
    htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
    hdef1

#print axioms symbolic_mask948_legacy_reuse

end Jsp404.SixExactFloorKernel
