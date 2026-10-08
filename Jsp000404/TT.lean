import Mathlib

set_option maxHeartbeats 1600000

namespace R2N4

open List

/-- **Scalar model of the `n = 4` six-centre terminal geometry.** -/
structure N4Model where
  lam : ℝ
  p : ℝ
  hlam : 0 < lam
  hp : 4 * lam <= p ∧ p < 5 * lam
  t : Fin 5 → ℝ
  ht : StrictMono t
  ht0 : 0 <= t 0
  ht4 : t 4 <= p - 4 * lam
  d : Fin 5 → Fin 5 → ℝ
  hcor : ∀ i j : Fin 5, i < j →
    t i + lam ≤ d i j ∧ d i j ≤ p - lam + t j
  htr : ∀ i j k : Fin 5, i < j → j < k →
    (d i j + lam ≤ d j k ∧ d i j < d i k ∧ d i k < d j k) ∨
    (d j k + lam ≤ d i j ∧ d j k < d i k ∧ d i k < d i j)
abbrev RowSig1 (lam p tl : ℝ) (x0 x1 x2 x3 : ℝ) : Prop :=
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 3 * lam)

abbrev RowSig2 (lam p tl : ℝ) (x0 x1 x2 x3 : ℝ) : Prop :=
    (3 * lam <= (x0 - tl) ∧ (x0 - tl) < 4 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 3 * lam <= (x1 - x0) ∧ (x1 - x0) < 4 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 3 * lam <= (x2 - x1) ∧ (x2 - x1) < 4 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 3 * lam <= (x3 - x2) ∧ (x3 - x2) < 4 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 3 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 4 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 3 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 3 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 3 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ 2 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 3 * lam)


theorem mem4or {u x0 x1 x2 x3 : ℝ} (h : u ∈ [x0, x1, x2, x3]) :
    u = x0 ∨ u = x1 ∨ u = x2 ∨ u = x3 := by
  simpa using h

/-- A value occurring twice in a 4-list occupies an ordered pair of slots. -/
theorem two_slots {v c0 c1 c2 c3 : ℝ} (h : 2 ≤ List.count v [c0, c1, c2, c3]) :
    (c0 = v ∧ c1 = v) ∨ (c0 = v ∧ c2 = v) ∨ (c0 = v ∧ c3 = v) ∨
    (c1 = v ∧ c2 = v) ∨ (c1 = v ∧ c3 = v) ∨ (c2 = v ∧ c3 = v) := by
  classical
  by_cases h0 : c0 = v <;> by_cases h1 : c1 = v <;> by_cases h2 : c2 = v <;>
    by_cases h3 : c3 = v <;> simp_all [List.count]


abbrev MSig1_0 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3], 2 * lam ≤ z - tl) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 6 * lam) ∧
    (c0 - tl < 3 * lam ∨ c1 - tl < 3 * lam ∨ c2 - tl < 3 * lam ∨ c3 - tl < 3 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam)

abbrev MSig1_2 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    ((c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z))) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 7 * lam) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam)

abbrev MSig2_3 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    ((c0 < c1 ∧ 3 * lam ≤ c1 - c0 ∧ c1 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 3 * lam ≤ c2 - c0 ∧ c2 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 3 * lam ≤ c3 - c0 ∧ c3 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c1 < c0 ∧ 3 * lam ≤ c0 - c1 ∧ c0 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c2 ∧ 3 * lam ≤ c2 - c1 ∧ c2 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 3 * lam ≤ c3 - c1 ∧ c3 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c2 < c0 ∧ 3 * lam ≤ c0 - c2 ∧ c0 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 3 * lam ≤ c1 - c2 ∧ c1 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c3 ∧ 3 * lam ≤ c3 - c2 ∧ c3 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c3 < c0 ∧ 3 * lam ≤ c0 - c3 ∧ c0 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 3 * lam ≤ c1 - c3 ∧ c1 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 3 * lam ≤ c2 - c3 ∧ c2 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z))) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 8 * lam) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam)

theorem n4l_tA_3_0_2 (m : N4Model)
    (h1 : MSig2_3 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4))
    (h2 : MSig1_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4))
    (h4 : MSig1_2 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4)) : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht4b := m.ht4
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  obtain ⟨h1bigk, _, h1emin, h1emax⟩ := h1
  obtain ⟨h2elo, _, _, _⟩ := h2
  obtain ⟨h4bigk, _, _, _⟩ := h4
  have u2e0 := h2elo (m.d 0 2) (by simp)
  have u2e1 := h2elo (m.d 1 2) (by simp)
  have u2e2 := h2elo (m.d 2 3) (by simp)
  have u2e3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · rcases h1bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
                      · obtain ⟨p10_0, p10_1, p10_2, p10_3⟩ := h10c
                        linarith only [h6, h9, hc01, hc34, hlam, hphi, ht0b, ht4b, p10_0, p10_1, p10_2, p10_3]
                      · obtain ⟨p10_0, p10_1, p10_2, p10_3⟩ := h10c
                        linarith only [h6, h9, hc01, hc34, hlam, hphi, ht0b, ht4b, p10_0, p10_1, p10_2, p10_3]
                      · obtain ⟨p10_0, p10_1, p10_2, p10_3⟩ := h10c
                        rcases p10_3 (m.d 1 2) (by simp) with h13 | h13
                        · linarith only [h0, h13, hlam]
                        · linarith only [h13, h7, hlam]
                      · obtain ⟨p10_0, p10_1, p10_2, p10_3⟩ := h10c
                        linarith only [h0, hlam, p10_0, p10_1, p10_2, p10_3]
                      · obtain ⟨p10_0, p10_1, p10_2, p10_3⟩ := h10c
                        linarith only [h0, h6, h9, hc02, hc34, hlam, hphi, ht0b, ht4b, p10_0, p10_1, p10_2, p10_3]
                      · obtain ⟨p10_0, p10_1, p10_2, p10_3⟩ := h10c
                        linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht4b, p10_0, p10_1, p10_2, p10_3]
                      · obtain ⟨p10_0, p10_1, p10_2, p10_3⟩ := h10c
                        linarith only [h1, hlam, p10_0, p10_1, p10_2, p10_3]
                      · obtain ⟨p10_0, p10_1, p10_2, p10_3⟩ := h10c
                        linarith only [h6, hlam, p10_0, p10_1, p10_2, p10_3]
                      · obtain ⟨p10_0, p10_1, p10_2, p10_3⟩ := h10c
                        linarith only [h1, h7, hc01, hc24, hlam, hphi, ht0b, ht4b, p10_0, p10_1, p10_2, p10_3]
                      · obtain ⟨p10_0, p10_1, p10_2, p10_3⟩ := h10c
                        linarith only [h2, hlam, p10_0, p10_1, p10_2, p10_3]
                      · obtain ⟨p10_0, p10_1, p10_2, p10_3⟩ := h10c
                        linarith only [h7, hlam, p10_0, p10_1, p10_2, p10_3]
                      · obtain ⟨p10_0, p10_1, p10_2, p10_3⟩ := h10c
                        linarith only [h8, hlam, p10_0, p10_1, p10_2, p10_3]
                    · rcases h1bigk with h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c
                      · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                        linarith only [h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht4b, p25_0, p25_1, p25_2, p25_3]
                      · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                        linarith only [h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht4b, p25_0, p25_1, p25_2, p25_3]
                      · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                        linarith only [h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht4b, p25_0, p25_1, p25_2, p25_3]
                      · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                        linarith only [h0, hlam, p25_0, p25_1, p25_2, p25_3]
                      · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                        linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht4b, p25_0, p25_1, p25_2, p25_3]
                      · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                        linarith only [h0, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht4b, p25_0, p25_1, p25_2, p25_3]
                      · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                        linarith only [h1, hlam, p25_0, p25_1, p25_2, p25_3]
                      · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                        linarith only [h6, hlam, p25_0, p25_1, p25_2, p25_3]
                      · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                        linarith only [h8, h9, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht4b, p25_0, p25_1, p25_2, p25_3]
                      · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                        linarith only [h2, hlam, p25_0, p25_1, p25_2, p25_3]
                      · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                        linarith only [h7, hlam, p25_0, p25_1, p25_2, p25_3]
                      · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                        linarith only [h8, hlam, p25_0, p25_1, p25_2, p25_3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                    · linarith only [h38, h6, h8, hlam]
                    · rcases h1bigk with h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c
                      · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                        linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht4b, p40_0, p40_1, p40_2, p40_3]
                      · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                        rcases p40_3 (m.d 1 2) (by simp) with h42 | h42
                        · linarith only [h0, h42, hlam]
                        · linarith only [h42, h6, hlam]
                      · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                        rcases p40_3 (m.d 1 2) (by simp) with h45 | h45
                        · linarith only [h0, h45, hlam]
                        · linarith only [h45, h7, hlam]
                      · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                        linarith only [h0, hlam, p40_0, p40_1, p40_2, p40_3]
                      · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                        linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht4b, p40_0, p40_1, p40_2, p40_3]
                      · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                        linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht4b, p40_0, p40_1, p40_2, p40_3]
                      · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                        linarith only [h1, hlam, p40_0, p40_1, p40_2, p40_3]
                      · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                        linarith only [h6, hlam, p40_0, p40_1, p40_2, p40_3]
                      · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                        linarith only [h8, hlam, p40_0, p40_1, p40_2, p40_3]
                      · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                        linarith only [h2, hlam, p40_0, p40_1, p40_2, p40_3]
                      · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                        linarith only [h7, hlam, p40_0, p40_1, p40_2, p40_3]
                      · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                        linarith only [h2, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht4b, p40_0, p40_1, p40_2, p40_3]
                · linarith only [h4, h7, hc12, hlam, hphi, u2e0]
              · linarith only [h3, h6, hc12, hlam, hphi, u2e0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
              · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
                · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                  · linarith only [h2, h5, h61, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                    · linarith only [h1, h5, h59, h63, hlam]
                    · rcases h1bigk with h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c
                      · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                        linarith only [h60, h63, hc01, hc23, hlam, hphi, ht0b, ht34, ht4b, p65_0, p65_1, p65_2, p65_3]
                      · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                        rcases p65_3 (m.d 1 2) (by simp) with h67 | h67
                        · linarith only [h0, h67, hlam]
                        · linarith only [h59, h67, hlam]
                      · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                        rcases p65_3 (m.d 1 2) (by simp) with h70 | h70
                        · linarith only [h0, h70, hlam]
                        · linarith only [h60, h70, hlam]
                      · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                        linarith only [h0, hlam, p65_0, p65_1, p65_2, p65_3]
                      · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                        linarith only [h0, h59, hc01, hc23, hlam, hphi, ht0b, ht34, ht4b, p65_0, p65_1, p65_2, p65_3]
                      · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                        linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht4b, p65_0, p65_1, p65_2, p65_3]
                      · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                        linarith only [h1, hlam, p65_0, p65_1, p65_2, p65_3]
                      · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                        linarith only [h59, hlam, p65_0, p65_1, p65_2, p65_3]
                      · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                        linarith only [h61, hlam, p65_0, p65_1, p65_2, p65_3]
                      · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                        linarith only [h2, hlam, p65_0, p65_1, p65_2, p65_3]
                      · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                        linarith only [h60, hlam, p65_0, p65_1, p65_2, p65_3]
                      · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                        linarith only [h2, h59, hc01, hc23, hlam, hphi, ht0b, ht34, ht4b, p65_0, p65_1, p65_2, p65_3]
                · linarith only [h4, h60, hc12, hlam, hphi, u2e0]
              · linarith only [h3, h59, hc12, hlam, hphi, u2e0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h84 | h84
            · linarith only [h3, h4, h84, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
              · rcases m.htr 1 2 4 (by decide) (by decide) with h87 | h87
                · linarith only [h0, h4, h87, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
                  · linarith only [h86, h87, h89, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                    · linarith only [h0, h4, h86, h91, hlam]
                    · rcases h1bigk with h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c
                      · obtain ⟨p93_0, p93_1, p93_2, p93_3⟩ := h93c
                        linarith only [h86, hc01, hc23, hlam, hphi, ht0b, ht34, ht4b, p93_0, p93_1, p93_2, p93_3]
                      · obtain ⟨p93_0, p93_1, p93_2, p93_3⟩ := h93c
                        rcases p93_3 (m.d 1 2) (by simp) with h95 | h95
                        · linarith only [h0, h95, hlam]
                        · linarith only [h86, h95, hlam]
                      · obtain ⟨p93_0, p93_1, p93_2, p93_3⟩ := h93c
                        linarith only [h86, h87, hc01, hc23, hlam, hphi, ht0b, ht34, ht4b, p93_0, p93_1, p93_2, p93_3]
                      · obtain ⟨p93_0, p93_1, p93_2, p93_3⟩ := h93c
                        linarith only [h0, hlam, p93_0, p93_1, p93_2, p93_3]
                      · obtain ⟨p93_0, p93_1, p93_2, p93_3⟩ := h93c
                        linarith only [h0, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht4b, p93_0, p93_1, p93_2, p93_3, u2e3]
                      · obtain ⟨p93_0, p93_1, p93_2, p93_3⟩ := h93c
                        linarith only [h87, hlam, p93_0, p93_1, p93_2, p93_3]
                      · obtain ⟨p93_0, p93_1, p93_2, p93_3⟩ := h93c
                        linarith only [h1, hlam, p93_0, p93_1, p93_2, p93_3]
                      · obtain ⟨p93_0, p93_1, p93_2, p93_3⟩ := h93c
                        linarith only [h86, hlam, p93_0, p93_1, p93_2, p93_3]
                      · obtain ⟨p93_0, p93_1, p93_2, p93_3⟩ := h93c
                        linarith only [h89, hlam, p93_0, p93_1, p93_2, p93_3]
                      · obtain ⟨p93_0, p93_1, p93_2, p93_3⟩ := h93c
                        linarith only [h2, hlam, p93_0, p93_1, p93_2, p93_3]
                      · obtain ⟨p93_0, p93_1, p93_2, p93_3⟩ := h93c
                        linarith only [h86, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht4b, p93_0, p93_1, p93_2, p93_3]
                      · obtain ⟨p93_0, p93_1, p93_2, p93_3⟩ := h93c
                        linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht4b, p93_0, p93_1, p93_2, p93_3]
              · linarith only [h3, h4, h86, hc12, hlam, hphi, u2e3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h109 | h109
          · rcases m.htr 0 3 4 (by decide) (by decide) with h110 | h110
            · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
              · linarith only [h0, h109, h111, h3, hc01, hc24, hlam, hphi, ht0b, ht4b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
                · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h115 | h115
                    · rcases h1bigk with h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c
                      · obtain ⟨p116_0, p116_1, p116_2, p116_3⟩ := h116c
                        linarith only [h113, hc01, hc24, hlam, hphi, ht0b, ht4b, p116_0, p116_1, p116_2, p116_3]
                      · obtain ⟨p116_0, p116_1, p116_2, p116_3⟩ := h116c
                        linarith only [h111, h113, h115, hc01, hc34, hlam, hphi, ht0b, ht4b, p116_0, p116_1, p116_2, p116_3]
                      · obtain ⟨p116_0, p116_1, p116_2, p116_3⟩ := h116c
                        rcases p116_3 (m.d 1 2) (by simp) with h119 | h119
                        · linarith only [h0, h119, hlam]
                        · linarith only [h113, h119, hlam]
                      · obtain ⟨p116_0, p116_1, p116_2, p116_3⟩ := h116c
                        linarith only [h0, hlam, p116_0, p116_1, p116_2, p116_3]
                      · obtain ⟨p116_0, p116_1, p116_2, p116_3⟩ := h116c
                        linarith only [h111, hlam, p116_0, p116_1, p116_2, p116_3]
                      · obtain ⟨p116_0, p116_1, p116_2, p116_3⟩ := h116c
                        linarith only [h0, h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht4b, p116_0, p116_1, p116_2, p116_3, u2e2]
                      · obtain ⟨p116_0, p116_1, p116_2, p116_3⟩ := h116c
                        linarith only [h1, hlam, p116_0, p116_1, p116_2, p116_3]
                      · obtain ⟨p116_0, p116_1, p116_2, p116_3⟩ := h116c
                        linarith only [h113, hc13, hc24, hlam, hphi, ht01, ht0b, ht4b, p116_0, p116_1, p116_2, p116_3]
                      · obtain ⟨p116_0, p116_1, p116_2, p116_3⟩ := h116c
                        linarith only [h1, hc01, hc14, hlam, hphi, ht0b, ht4b, p116_0, p116_1, p116_2, p116_3]
                      · obtain ⟨p116_0, p116_1, p116_2, p116_3⟩ := h116c
                        linarith only [h2, hlam, p116_0, p116_1, p116_2, p116_3]
                      · obtain ⟨p116_0, p116_1, p116_2, p116_3⟩ := h116c
                        linarith only [h113, hlam, p116_0, p116_1, p116_2, p116_3]
                      · obtain ⟨p116_0, p116_1, p116_2, p116_3⟩ := h116c
                        linarith only [h114, hlam, p116_0, p116_1, p116_2, p116_3]
                    · linarith only [h0, h113, h115, h3, hlam]
                  · linarith only [h111, h113, h114, hlam]
                · linarith only [h109, h113, h3, hc12, hlam, hphi, u2e2]
            · linarith only [h109, h110, h3, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h135 | h135
            · rcases m.htr 1 2 3 (by decide) (by decide) with h136 | h136
              · linarith only [h136, h3, hc02, hlam, hphi, u2e1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h138 | h138
                · linarith only [h0, h109, h138, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h140 | h140
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                    · rcases h1bigk with h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c
                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                        rcases p142_3 (m.d 1 2) (by simp) with h143 | h143
                        · linarith only [h143, hlam, p142_0, p142_1, p142_2, p142_3]
                        · rcases p142_3 (m.d 1 4) (by simp) with h145 | h145
                          · linarith only [h145, h2, hlam]
                          · linarith only [h138, h145, hlam]
                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                        linarith only [h140, hc01, hc34, hlam, hphi, ht0b, ht4b, p142_0, p142_1, p142_2, p142_3]
                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                        rcases p142_3 (m.d 1 2) (by simp) with h149 | h149
                        · linarith only [h0, h149, hlam]
                        · rcases p142_3 (m.d 1 4) (by simp) with h151 | h151
                          · linarith only [h151, hlam, p142_0, p142_1, p142_2, p142_3]
                          · rcases h1emax with h153 | h153 | h153 | h153
                            · linarith only [h138, h153, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht4b, p142_0, p142_1, p142_2, p142_3]
                            · rcases h1emin with h155 | h155 | h155 | h155
                              · rcases h4bigk with h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c
                                · obtain ⟨p156_0, p156_1, p156_2, p156_3⟩ := h156c
                                  linarith only [h109, h138, h141, hc12, hlam, hphi, p156_0, p156_1, p156_2, p156_3, u2e2]
                                · obtain ⟨p156_0, p156_1, p156_2, p156_3⟩ := h156c
                                  linarith only [h109, hlam, p156_0, p156_1, p156_2, p156_3]
                                · obtain ⟨p156_0, p156_1, p156_2, p156_3⟩ := h156c
                                  rcases p156_3 (m.d 1 4) (by simp) with h159 | h159
                                  · linarith only [h159, h2, hlam]
                                  · linarith only [h140, h159, hlam]
                                · obtain ⟨p156_0, p156_1, p156_2, p156_3⟩ := h156c
                                  linarith only [h2, hlam, p156_0, p156_1, p156_2, p156_3]
                                · obtain ⟨p156_0, p156_1, p156_2, p156_3⟩ := h156c
                                  linarith only [h138, hlam, p156_0, p156_1, p156_2, p156_3]
                                · obtain ⟨p156_0, p156_1, p156_2, p156_3⟩ := h156c
                                  linarith only [hc01, hc34, hlam, hphi, ht0b, ht4b, p142_0, p142_1, p142_2, p142_3, p156_0, p156_1, p156_2, p156_3]
                                · obtain ⟨p156_0, p156_1, p156_2, p156_3⟩ := h156c
                                  linarith only [h138, h141, h2, hc12, hlam, hphi, p156_0, p156_1, p156_2, p156_3, u2e2]
                                · obtain ⟨p156_0, p156_1, p156_2, p156_3⟩ := h156c
                                  linarith only [h138, h141, hc12, hlam, hphi, p156_0, p156_1, p156_2, p156_3, u2e2]
                                · obtain ⟨p156_0, p156_1, p156_2, p156_3⟩ := h156c
                                  rcases p156_3 (m.d 1 4) (by simp) with h167 | h167
                                  · linarith only [h138, h167, hlam]
                                  · linarith only [h140, h167, hlam]
                                · obtain ⟨p156_0, p156_1, p156_2, p156_3⟩ := h156c
                                  linarith only [h135, hlam, p156_0, p156_1, p156_2, p156_3]
                                · obtain ⟨p156_0, p156_1, p156_2, p156_3⟩ := h156c
                                  linarith only [h140, hlam, p156_0, p156_1, p156_2, p156_3]
                                · obtain ⟨p156_0, p156_1, p156_2, p156_3⟩ := h156c
                                  linarith only [h141, hlam, p156_0, p156_1, p156_2, p156_3]
                              · linarith only [h138, h155, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht4b, p142_0, p142_1, p142_2, p142_3]
                              · linarith only [h1, h155, h3, hlam, ht12, u2e2]
                              · linarith only [h155, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht4b, p142_0, p142_1, p142_2, p142_3]
                            · rcases h1emin with h176 | h176 | h176 | h176
                              · rcases h4bigk with h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c
                                · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                  linarith only [h109, h138, h141, hc12, hlam, hphi, p177_0, p177_1, p177_2, p177_3, u2e2]
                                · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                  linarith only [h109, hlam, p177_0, p177_1, p177_2, p177_3]
                                · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                  rcases p177_3 (m.d 1 4) (by simp) with h180 | h180
                                  · linarith only [h180, h2, hlam]
                                  · linarith only [h140, h180, hlam]
                                · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                  linarith only [h2, hlam, p177_0, p177_1, p177_2, p177_3]
                                · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                  linarith only [h138, hlam, p177_0, p177_1, p177_2, p177_3]
                                · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                  linarith only [hc01, hc34, hlam, hphi, ht0b, ht4b, p142_0, p142_1, p142_2, p142_3, p177_0, p177_1, p177_2, p177_3]
                                · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                  linarith only [h138, h141, h2, hc12, hlam, hphi, p177_0, p177_1, p177_2, p177_3, u2e2]
                                · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                  linarith only [h138, h141, hc12, hlam, hphi, p177_0, p177_1, p177_2, p177_3, u2e2]
                                · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                  rcases p177_3 (m.d 1 4) (by simp) with h188 | h188
                                  · linarith only [h138, h188, hlam]
                                  · linarith only [h140, h188, hlam]
                                · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                  linarith only [h135, hlam, p177_0, p177_1, p177_2, p177_3]
                                · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                  linarith only [h140, hlam, p177_0, p177_1, p177_2, p177_3]
                                · obtain ⟨p177_0, p177_1, p177_2, p177_3⟩ := h177c
                                  linarith only [h141, hlam, p177_0, p177_1, p177_2, p177_3]
                              · linarith only [h138, h176, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht4b, p142_0, p142_1, p142_2, p142_3]
                              · linarith only [h153, h176, hlam, hplo]
                              · linarith only [h176, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht4b, p142_0, p142_1, p142_2, p142_3]
                            · rcases h1emin with h197 | h197 | h197 | h197
                              · rcases h4bigk with h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c
                                · obtain ⟨p198_0, p198_1, p198_2, p198_3⟩ := h198c
                                  linarith only [h109, h138, h141, hc12, hlam, hphi, p198_0, p198_1, p198_2, p198_3, u2e2]
                                · obtain ⟨p198_0, p198_1, p198_2, p198_3⟩ := h198c
                                  linarith only [h109, hlam, p198_0, p198_1, p198_2, p198_3]
                                · obtain ⟨p198_0, p198_1, p198_2, p198_3⟩ := h198c
                                  rcases p198_3 (m.d 1 4) (by simp) with h201 | h201
                                  · linarith only [h2, h201, hlam]
                                  · linarith only [h140, h201, hlam]
                                · obtain ⟨p198_0, p198_1, p198_2, p198_3⟩ := h198c
                                  linarith only [h2, hlam, p198_0, p198_1, p198_2, p198_3]
                                · obtain ⟨p198_0, p198_1, p198_2, p198_3⟩ := h198c
                                  linarith only [h138, hlam, p198_0, p198_1, p198_2, p198_3]
                                · obtain ⟨p198_0, p198_1, p198_2, p198_3⟩ := h198c
                                  linarith only [hc01, hc34, hlam, hphi, ht0b, ht4b, p142_0, p142_1, p142_2, p142_3, p198_0, p198_1, p198_2, p198_3]
                                · obtain ⟨p198_0, p198_1, p198_2, p198_3⟩ := h198c
                                  linarith only [h138, h141, h2, hc12, hlam, hphi, p198_0, p198_1, p198_2, p198_3, u2e2]
                                · obtain ⟨p198_0, p198_1, p198_2, p198_3⟩ := h198c
                                  linarith only [h138, h141, hc12, hlam, hphi, p198_0, p198_1, p198_2, p198_3, u2e2]
                                · obtain ⟨p198_0, p198_1, p198_2, p198_3⟩ := h198c
                                  rcases p198_3 (m.d 1 4) (by simp) with h209 | h209
                                  · linarith only [h138, h209, hlam]
                                  · linarith only [h140, h209, hlam]
                                · obtain ⟨p198_0, p198_1, p198_2, p198_3⟩ := h198c
                                  linarith only [h135, hlam, p198_0, p198_1, p198_2, p198_3]
                                · obtain ⟨p198_0, p198_1, p198_2, p198_3⟩ := h198c
                                  linarith only [h140, hlam, p198_0, p198_1, p198_2, p198_3]
                                · obtain ⟨p198_0, p198_1, p198_2, p198_3⟩ := h198c
                                  linarith only [h141, hlam, p198_0, p198_1, p198_2, p198_3]
                              · linarith only [h138, h197, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht4b, p142_0, p142_1, p142_2, p142_3]
                              · linarith only [h1, h197, h3, hlam, ht12, u2e2]
                              · linarith only [h197, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht4b, p142_0, p142_1, p142_2, p142_3]
                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                        linarith only [h0, hlam, p142_0, p142_1, p142_2, p142_3]
                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                        linarith only [h136, hlam, p142_0, p142_1, p142_2, p142_3]
                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                        linarith only [h138, hlam, p142_0, p142_1, p142_2, p142_3]
                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                        linarith only [h1, hlam, p142_0, p142_1, p142_2, p142_3]
                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht4b, p142_0, p142_1, p142_2, p142_3]
                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                        linarith only [h1, hc01, hc14, hlam, hphi, ht0b, ht4b, p142_0, p142_1, p142_2, p142_3]
                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                        linarith only [h2, hlam, p142_0, p142_1, p142_2, p142_3]
                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht4b, p142_0, p142_1, p142_2, p142_3]
                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                        linarith only [h140, hlam, p142_0, p142_1, p142_2, p142_3]
                    · linarith only [h109, h135, h141, hlam]
                  · linarith only [h135, h136, h140, h3, hc12, hlam, hphi, u2e2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h229 | h229
              · linarith only [h0, h229, h3, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h231 | h231
                · linarith only [h0, h109, h231, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h233 | h233
                  · linarith only [h1, h135, h233, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h235 | h235
                    · linarith only [h1, h135, h229, h235, hc12, hlam, hphi, u2e2]
                    · rcases h1bigk with h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c
                      · obtain ⟨p237_0, p237_1, p237_2, p237_3⟩ := h237c
                        rcases p237_3 (m.d 1 2) (by simp) with h238 | h238
                        · linarith only [h238, hlam, p237_0, p237_1, p237_2, p237_3]
                        · rcases p237_3 (m.d 1 4) (by simp) with h240 | h240
                          · linarith only [h2, h240, hlam]
                          · linarith only [h231, h240, hlam]
                      · obtain ⟨p237_0, p237_1, p237_2, p237_3⟩ := h237c
                        rcases p237_3 (m.d 1 2) (by simp) with h243 | h243
                        · linarith only [h0, h243, hlam]
                        · rcases p237_3 (m.d 1 4) (by simp) with h245 | h245
                          · linarith only [h2, h245, hlam]
                          · linarith only [h233, h245, hlam]
                      · obtain ⟨p237_0, p237_1, p237_2, p237_3⟩ := h237c
                        rcases p237_3 (m.d 1 2) (by simp) with h248 | h248
                        · linarith only [h0, h248, hlam]
                        · rcases p237_3 (m.d 1 4) (by simp) with h250 | h250
                          · linarith only [h250, hlam, p237_0, p237_1, p237_2, p237_3]
                          · rcases h1emax with h252 | h252 | h252 | h252
                            · linarith only [h229, h233, h252, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht4b, p237_0, p237_1, p237_2, p237_3]
                            · rcases h1emin with h254 | h254 | h254 | h254
                              · rcases h4bigk with h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c
                                · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                  linarith only [h109, h229, h233, hc12, hlam, hphi, p255_0, p255_1, p255_2, p255_3, u2e3]
                                · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                  linarith only [h109, hlam, p255_0, p255_1, p255_2, p255_3]
                                · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                  linarith only [h135, hlam, p255_0, p255_1, p255_2, p255_3]
                                · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                  linarith only [h2, hlam, p255_0, p255_1, p255_2, p255_3]
                                · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                  linarith only [h231, hlam, p255_0, p255_1, p255_2, p255_3]
                                · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                  linarith only [h233, hlam, p255_0, p255_1, p255_2, p255_3]
                                · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                  linarith only [h2, h229, h233, hc12, hlam, hphi, p255_0, p255_1, p255_2, p255_3, u2e3]
                                · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                  linarith only [h229, h233, hc12, hlam, hphi, p255_0, p255_1, p255_2, p255_3, u2e3]
                                · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                  linarith only [h235, hlam, p255_0, p255_1, p255_2, p255_3]
                                · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                  rcases p255_3 (m.d 1 4) (by simp) with h265 | h265
                                  · linarith only [h233, h265, hlam]
                                  · rcases p255_3 (m.d 2 4) (by simp) with h267 | h267
                                    · linarith only [h235, h267, hlam]
                                    · linarith only [h109, h267, hlam]
                                · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                  rcases p255_3 (m.d 1 4) (by simp) with h270 | h270
                                  · linarith only [h233, h270, hlam]
                                  · rcases p255_3 (m.d 2 4) (by simp) with h272 | h272
                                    · linarith only [h235, h272, hlam]
                                    · linarith only [h231, h272, hlam]
                                · obtain ⟨p255_0, p255_1, p255_2, p255_3⟩ := h255c
                                  linarith only [h0, h109, hc12, hc34, hlam, hphi, ht23, p255_0, p255_1, p255_2, p255_3]
                              · linarith only [h229, h233, h254, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht4b, p237_0, p237_1, p237_2, p237_3]
                              · linarith only [h233, h254, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht4b, p237_0, p237_1, p237_2, p237_3]
                              · linarith only [h254, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht4b, p237_0, p237_1, p237_2, p237_3]
                            · rcases h1emin with h279 | h279 | h279 | h279
                              · rcases h4bigk with h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c
                                · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                                  linarith only [h109, h229, h233, hc12, hlam, hphi, p280_0, p280_1, p280_2, p280_3, u2e3]
                                · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                                  linarith only [h109, hlam, p280_0, p280_1, p280_2, p280_3]
                                · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                                  linarith only [h135, hlam, p280_0, p280_1, p280_2, p280_3]
                                · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                                  linarith only [h2, hlam, p280_0, p280_1, p280_2, p280_3]
                                · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                                  linarith only [h231, hlam, p280_0, p280_1, p280_2, p280_3]
                                · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                                  linarith only [h233, hlam, p280_0, p280_1, p280_2, p280_3]
                                · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                                  linarith only [h2, h229, h233, hc12, hlam, hphi, p280_0, p280_1, p280_2, p280_3, u2e3]
                                · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                                  linarith only [h229, h233, hc12, hlam, hphi, p280_0, p280_1, p280_2, p280_3, u2e3]
                                · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                                  linarith only [h235, hlam, p280_0, p280_1, p280_2, p280_3]
                                · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                                  rcases p280_3 (m.d 1 4) (by simp) with h290 | h290
                                  · linarith only [h233, h290, hlam]
                                  · rcases p280_3 (m.d 2 4) (by simp) with h292 | h292
                                    · linarith only [h235, h292, hlam]
                                    · linarith only [h109, h292, hlam]
                                · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                                  rcases p280_3 (m.d 1 4) (by simp) with h295 | h295
                                  · linarith only [h233, h295, hlam]
                                  · rcases p280_3 (m.d 2 4) (by simp) with h297 | h297
                                    · linarith only [h235, h297, hlam]
                                    · linarith only [h231, h297, hlam]
                                · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                                  linarith only [h0, h109, hc12, hc34, hlam, hphi, ht23, p280_0, p280_1, p280_2, p280_3]
                              · linarith only [h229, h233, h279, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht4b, p237_0, p237_1, p237_2, p237_3]
                              · linarith only [h233, h279, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht4b, p237_0, p237_1, p237_2, p237_3]
                              · linarith only [h279, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht4b, p237_0, p237_1, p237_2, p237_3]
                            · rcases h1emin with h304 | h304 | h304 | h304
                              · rcases h4bigk with h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h109, h229, h233, hc12, hlam, hphi, p305_0, p305_1, p305_2, p305_3, u2e3]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h109, hlam, p305_0, p305_1, p305_2, p305_3]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h135, hlam, p305_0, p305_1, p305_2, p305_3]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h2, hlam, p305_0, p305_1, p305_2, p305_3]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h231, hlam, p305_0, p305_1, p305_2, p305_3]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h233, hlam, p305_0, p305_1, p305_2, p305_3]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h2, h229, h233, hc12, hlam, hphi, p305_0, p305_1, p305_2, p305_3, u2e3]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h229, h233, hc12, hlam, hphi, p305_0, p305_1, p305_2, p305_3, u2e3]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h235, hlam, p305_0, p305_1, p305_2, p305_3]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  rcases p305_3 (m.d 1 4) (by simp) with h315 | h315
                                  · linarith only [h233, h315, hlam]
                                  · rcases p305_3 (m.d 2 4) (by simp) with h317 | h317
                                    · linarith only [h235, h317, hlam]
                                    · linarith only [h109, h317, hlam]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  rcases p305_3 (m.d 1 4) (by simp) with h320 | h320
                                  · linarith only [h233, h320, hlam]
                                  · rcases p305_3 (m.d 2 4) (by simp) with h322 | h322
                                    · linarith only [h235, h322, hlam]
                                    · linarith only [h231, h322, hlam]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h0, h109, hc12, hc34, hlam, hphi, ht23, p305_0, p305_1, p305_2, p305_3]
                              · linarith only [h229, h233, h304, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht4b, p237_0, p237_1, p237_2, p237_3]
                              · linarith only [h233, h304, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht4b, p237_0, p237_1, p237_2, p237_3]
                              · linarith only [h304, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht4b, p237_0, p237_1, p237_2, p237_3]
                      · obtain ⟨p237_0, p237_1, p237_2, p237_3⟩ := h237c
                        linarith only [h0, hlam, p237_0, p237_1, p237_2, p237_3]
                      · obtain ⟨p237_0, p237_1, p237_2, p237_3⟩ := h237c
                        linarith only [h229, hlam, p237_0, p237_1, p237_2, p237_3]
                      · obtain ⟨p237_0, p237_1, p237_2, p237_3⟩ := h237c
                        linarith only [h231, hlam, p237_0, p237_1, p237_2, p237_3]
                      · obtain ⟨p237_0, p237_1, p237_2, p237_3⟩ := h237c
                        linarith only [h1, hlam, p237_0, p237_1, p237_2, p237_3]
                      · obtain ⟨p237_0, p237_1, p237_2, p237_3⟩ := h237c
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht4b, p237_0, p237_1, p237_2, p237_3]
                      · obtain ⟨p237_0, p237_1, p237_2, p237_3⟩ := h237c
                        linarith only [h233, hlam, p237_0, p237_1, p237_2, p237_3]
                      · obtain ⟨p237_0, p237_1, p237_2, p237_3⟩ := h237c
                        linarith only [h2, hlam, p237_0, p237_1, p237_2, p237_3]
                      · obtain ⟨p237_0, p237_1, p237_2, p237_3⟩ := h237c
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht4b, p237_0, p237_1, p237_2, p237_3]
                      · obtain ⟨p237_0, p237_1, p237_2, p237_3⟩ := h237c
                        linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht4b, p237_0, p237_1, p237_2, p237_3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h338 | h338
        · rcases m.htr 0 2 4 (by decide) (by decide) with h339 | h339
          · linarith only [h0, h2, h339, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h341 | h341
            · linarith only [h1, h2, h341, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h343 | h343
              · rcases m.htr 1 2 4 (by decide) (by decide) with h344 | h344
                · linarith only [h0, h2, h344, hlam]
                · linarith only [h0, h2, h343, h344, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht4b, u2e3]
              · linarith only [h338, h339, h343, hc12, hlam, hphi, u2e3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h348 | h348
          · linarith only [h0, h2, h338, h348, hc12, hlam, hphi, u2e2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h350 | h350
            · linarith only [h1, h2, h350, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h352 | h352
              · linarith only [h0, h2, h338, h352, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht4b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h354 | h354
                · linarith only [h1, h2, h352, h354, hlam]
                · linarith only [h1, h2, h352, h354, hc12, hlam, hphi, u2e3]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h357 | h357
      · rcases m.htr 0 2 3 (by decide) (by decide) with h358 | h358
        · linarith only [h0, h1, h358, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h360 | h360
          · rcases m.htr 0 3 4 (by decide) (by decide) with h361 | h361
            · rcases m.htr 1 2 3 (by decide) (by decide) with h362 | h362
              · linarith only [h0, h1, h362, hlam]
              · linarith only [h0, h1, h362, hc12, hlam, hphi, u2e2]
            · linarith only [h0, h1, h358, h360, h361, hc12, hlam, hphi, u2e2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h366 | h366
            · rcases m.htr 1 2 3 (by decide) (by decide) with h367 | h367
              · linarith only [h0, h1, h367, hlam]
              · linarith only [h0, h1, h367, hc12, hlam, hphi, u2e2]
            · linarith only [h1, h357, h366, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h371 | h371
        · linarith only [h0, h1, h371, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h373 | h373
          · linarith only [h0, h357, h371, h373, hc12, hlam, hphi, u2e2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h375 | h375
            · rcases m.htr 1 2 3 (by decide) (by decide) with h376 | h376
              · linarith only [h0, h1, h376, hlam]
              · linarith only [h0, h1, h376, hc12, hlam, hphi, u2e2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h379 | h379
              · linarith only [h0, h1, h379, hlam]
              · linarith only [h0, h1, h379, hc12, hlam, hphi, u2e2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h382 | h382
    · rcases m.htr 0 1 4 (by decide) (by decide) with h383 | h383
      · rcases m.htr 0 2 3 (by decide) (by decide) with h384 | h384
        · rcases m.htr 0 2 4 (by decide) (by decide) with h385 | h385
          · rcases m.htr 0 3 4 (by decide) (by decide) with h386 | h386
            · rcases m.htr 1 2 3 (by decide) (by decide) with h387 | h387
              · rcases m.htr 1 2 4 (by decide) (by decide) with h388 | h388
                · rcases m.htr 1 3 4 (by decide) (by decide) with h389 | h389
                  · linarith only [h0, h382, h389, hc34, hlam, hphi, ht01, ht0b, ht12, ht4b, u2e1]
                  · linarith only [h0, h382, h386, h387, h389, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht4b, u2e1]
                · linarith only [h0, h383, h388, hlam]
              · linarith only [h0, h382, h387, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h394 | h394
              · rcases m.htr 1 2 4 (by decide) (by decide) with h395 | h395
                · rcases m.htr 1 3 4 (by decide) (by decide) with h396 | h396
                  · linarith only [h0, h382, h386, h396, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht4b, u2e1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h398 | h398
                    · linarith only [h382, h386, h394, h398, hlam]
                    · rcases h1bigk with h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c
                      · obtain ⟨p400_0, p400_1, p400_2, p400_3⟩ := h400c
                        linarith only [h0, hlam, p400_0, p400_1, p400_2, p400_3]
                      · obtain ⟨p400_0, p400_1, p400_2, p400_3⟩ := h400c
                        linarith only [h0, h394, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht4b, p400_0, p400_1, p400_2, p400_3, u2e1]
                      · obtain ⟨p400_0, p400_1, p400_2, p400_3⟩ := h400c
                        linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht12, ht4b, p400_0, p400_1, p400_2, p400_3, u2e1]
                      · obtain ⟨p400_0, p400_1, p400_2, p400_3⟩ := h400c
                        linarith only [hc01, hlam, hphi, ht12, p400_0, p400_1, p400_2, p400_3, u2e1]
                      · obtain ⟨p400_0, p400_1, p400_2, p400_3⟩ := h400c
                        linarith only [h394, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht4b, p400_0, p400_1, p400_2, p400_3, u2e1]
                      · obtain ⟨p400_0, p400_1, p400_2, p400_3⟩ := h400c
                        linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht4b, p400_0, p400_1, p400_2, p400_3, u2e1]
                      · obtain ⟨p400_0, p400_1, p400_2, p400_3⟩ := h400c
                        linarith only [h382, hlam, p400_0, p400_1, p400_2, p400_3]
                      · obtain ⟨p400_0, p400_1, p400_2, p400_3⟩ := h400c
                        linarith only [h394, hlam, p400_0, p400_1, p400_2, p400_3]
                      · obtain ⟨p400_0, p400_1, p400_2, p400_3⟩ := h400c
                        linarith only [h396, hlam, p400_0, p400_1, p400_2, p400_3]
                      · obtain ⟨p400_0, p400_1, p400_2, p400_3⟩ := h400c
                        linarith only [h383, hlam, p400_0, p400_1, p400_2, p400_3]
                      · obtain ⟨p400_0, p400_1, p400_2, p400_3⟩ := h400c
                        linarith only [h395, hlam, p400_0, p400_1, p400_2, p400_3]
                      · obtain ⟨p400_0, p400_1, p400_2, p400_3⟩ := h400c
                        linarith only [h383, h394, hc01, hc23, hlam, hphi, ht0b, ht34, ht4b, p400_0, p400_1, p400_2, p400_3]
                · linarith only [h0, h383, h395, hlam]
              · linarith only [h0, h382, h394, hlam]
          · linarith only [h0, h383, h385, hlam]
        · linarith only [h0, h382, h384, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h417 | h417
        · rcases m.htr 0 2 4 (by decide) (by decide) with h418 | h418
          · rcases m.htr 0 3 4 (by decide) (by decide) with h419 | h419
            · linarith only [h382, h383, h419, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h421 | h421
              · rcases m.htr 1 2 4 (by decide) (by decide) with h422 | h422
                · rcases m.htr 1 3 4 (by decide) (by decide) with h423 | h423
                  · linarith only [h382, h383, h423, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h425 | h425
                    · linarith only [h382, h383, h421, h423, h425, hlam]
                    · rcases h1bigk with h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c
                      · obtain ⟨p427_0, p427_1, p427_2, p427_3⟩ := h427c
                        linarith only [h0, hlam, p427_0, p427_1, p427_2, p427_3]
                      · obtain ⟨p427_0, p427_1, p427_2, p427_3⟩ := h427c
                        linarith only [h383, h421, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht4b, p427_0, p427_1, p427_2, p427_3]
                      · obtain ⟨p427_0, p427_1, p427_2, p427_3⟩ := h427c
                        linarith only [h383, hlam, p427_0, p427_1, p427_2, p427_3]
                      · obtain ⟨p427_0, p427_1, p427_2, p427_3⟩ := h427c
                        linarith only [hc01, hlam, hphi, ht12, p427_0, p427_1, p427_2, p427_3, u2e1]
                      · obtain ⟨p427_0, p427_1, p427_2, p427_3⟩ := h427c
                        linarith only [h421, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht4b, p427_0, p427_1, p427_2, p427_3, u2e1]
                      · obtain ⟨p427_0, p427_1, p427_2, p427_3⟩ := h427c
                        linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht4b, p427_0, p427_1, p427_2, p427_3, u2e1]
                      · obtain ⟨p427_0, p427_1, p427_2, p427_3⟩ := h427c
                        linarith only [h382, hlam, p427_0, p427_1, p427_2, p427_3]
                      · obtain ⟨p427_0, p427_1, p427_2, p427_3⟩ := h427c
                        linarith only [h421, hlam, p427_0, p427_1, p427_2, p427_3]
                      · obtain ⟨p427_0, p427_1, p427_2, p427_3⟩ := h427c
                        linarith only [h423, hlam, p427_0, p427_1, p427_2, p427_3]
                      · obtain ⟨p427_0, p427_1, p427_2, p427_3⟩ := h427c
                        linarith only [hc01, hc14, hlam, hphi, p427_0, p427_1, p427_2, p427_3]
                      · obtain ⟨p427_0, p427_1, p427_2, p427_3⟩ := h427c
                        linarith only [h422, hlam, p427_0, p427_1, p427_2, p427_3]
                      · obtain ⟨p427_0, p427_1, p427_2, p427_3⟩ := h427c
                        linarith only [h421, h422, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht4b, p427_0, p427_1, p427_2, p427_3, u2e1]
                · linarith only [h0, h382, h421, h422, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht4b, u2e3]
              · linarith only [h0, h382, h421, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h442 | h442
            · linarith only [h0, h382, h418, h442, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h444 | h444
              · rcases m.htr 1 2 4 (by decide) (by decide) with h445 | h445
                · linarith only [h0, h382, h418, h444, h445, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht4b, u2e1]
                · linarith only [h0, h382, h444, h445, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht4b, u2e3]
              · linarith only [h0, h382, h444, hlam]
        · linarith only [h0, h382, h417, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h450 | h450
      · rcases m.htr 0 2 3 (by decide) (by decide) with h451 | h451
        · rcases m.htr 0 2 4 (by decide) (by decide) with h452 | h452
          · rcases m.htr 0 3 4 (by decide) (by decide) with h453 | h453
            · rcases m.htr 1 2 3 (by decide) (by decide) with h454 | h454
              · rcases m.htr 1 2 4 (by decide) (by decide) with h455 | h455
                · rcases m.htr 1 3 4 (by decide) (by decide) with h456 | h456
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h457 | h457
                    · rcases h1bigk with h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c
                      · obtain ⟨p458_0, p458_1, p458_2, p458_3⟩ := h458c
                        linarith only [h0, hlam, p458_0, p458_1, p458_2, p458_3]
                      · obtain ⟨p458_0, p458_1, p458_2, p458_3⟩ := h458c
                        linarith only [h382, hlam, p458_0, p458_1, p458_2, p458_3]
                      · obtain ⟨p458_0, p458_1, p458_2, p458_3⟩ := h458c
                        linarith only [h382, h454, h455, h457, hc12, hc34, hlam, hphi, ht01, ht0b, ht4b, p458_0, p458_1, p458_2, p458_3]
                      · obtain ⟨p458_0, p458_1, p458_2, p458_3⟩ := h458c
                        linarith only [hc01, hc12, hlam, hphi, p458_0, p458_1, p458_2, p458_3]
                      · obtain ⟨p458_0, p458_1, p458_2, p458_3⟩ := h458c
                        linarith only [h382, hc01, hc12, hlam, hphi, p458_0, p458_1, p458_2, p458_3]
                      · obtain ⟨p458_0, p458_1, p458_2, p458_3⟩ := h458c
                        linarith only [h455, h457, hc34, hlam, hphi, ht01, ht0b, ht12, ht4b, p458_0, p458_1, p458_2, p458_3, u2e1]
                      · obtain ⟨p458_0, p458_1, p458_2, p458_3⟩ := h458c
                        linarith only [h450, h455, h457, hc13, hc34, hlam, hphi, ht01, ht0b, ht4b, p458_0, p458_1, p458_2, p458_3]
                      · obtain ⟨p458_0, p458_1, p458_2, p458_3⟩ := h458c
                        linarith only [h454, hlam, p458_0, p458_1, p458_2, p458_3]
                      · obtain ⟨p458_0, p458_1, p458_2, p458_3⟩ := h458c
                        linarith only [h454, h455, h457, hc34, hlam, hphi, ht01, ht0b, ht12, ht4b, p458_0, p458_1, p458_2, p458_3, u2e1]
                      · obtain ⟨p458_0, p458_1, p458_2, p458_3⟩ := h458c
                        linarith only [h450, hlam, p458_0, p458_1, p458_2, p458_3]
                      · obtain ⟨p458_0, p458_1, p458_2, p458_3⟩ := h458c
                        linarith only [h455, hlam, p458_0, p458_1, p458_2, p458_3]
                      · obtain ⟨p458_0, p458_1, p458_2, p458_3⟩ := h458c
                        linarith only [h456, hlam, p458_0, p458_1, p458_2, p458_3]
                    · linarith only [h0, h450, h456, h457, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht4b, u2e1]
                  · linarith only [h382, h450, h456, hlam]
                · linarith only [h382, h450, h454, h455, hlam]
              · linarith only [h0, h454, hc01, hlam, hphi, ht12, u2e2]
            · linarith only [h382, h450, h453, hlam]
          · linarith only [h382, h450, h451, h452, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h477 | h477
          · rcases m.htr 0 3 4 (by decide) (by decide) with h478 | h478
            · rcases m.htr 1 2 3 (by decide) (by decide) with h479 | h479
              · linarith only [h0, h451, h479, hc01, hlam, hphi, ht12, u2e1]
              · linarith only [h0, h479, hc01, hlam, hphi, ht12, u2e2]
            · linarith only [h0, h450, h451, h478, hlam]
          · linarith only [h0, h450, h477, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h484 | h484
        · rcases m.htr 0 2 4 (by decide) (by decide) with h485 | h485
          · rcases m.htr 0 3 4 (by decide) (by decide) with h486 | h486
            · rcases m.htr 1 2 3 (by decide) (by decide) with h487 | h487
              · rcases m.htr 1 2 4 (by decide) (by decide) with h488 | h488
                · rcases m.htr 1 3 4 (by decide) (by decide) with h489 | h489
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h490 | h490
                    · rcases h1bigk with h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c
                      · obtain ⟨p491_0, p491_1, p491_2, p491_3⟩ := h491c
                        linarith only [h0, hlam, p491_0, p491_1, p491_2, p491_3]
                      · obtain ⟨p491_0, p491_1, p491_2, p491_3⟩ := h491c
                        linarith only [h382, hlam, p491_0, p491_1, p491_2, p491_3]
                      · obtain ⟨p491_0, p491_1, p491_2, p491_3⟩ := h491c
                        linarith only [h450, hlam, p491_0, p491_1, p491_2, p491_3]
                      · obtain ⟨p491_0, p491_1, p491_2, p491_3⟩ := h491c
                        linarith only [hc01, hlam, hphi, ht12, p491_0, p491_1, p491_2, p491_3, u2e1]
                      · obtain ⟨p491_0, p491_1, p491_2, p491_3⟩ := h491c
                        linarith only [hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht4b, p491_0, p491_1, p491_2, p491_3, u2e1]
                      · obtain ⟨p491_0, p491_1, p491_2, p491_3⟩ := h491c
                        linarith only [h450, hc01, hlam, hphi, ht12, p491_0, p491_1, p491_2, p491_3, u2e1]
                      · obtain ⟨p491_0, p491_1, p491_2, p491_3⟩ := h491c
                        linarith only [hc01, hc13, hlam, hphi, p491_0, p491_1, p491_2, p491_3]
                      · obtain ⟨p491_0, p491_1, p491_2, p491_3⟩ := h491c
                        linarith only [h487, hlam, p491_0, p491_1, p491_2, p491_3]
                      · obtain ⟨p491_0, p491_1, p491_2, p491_3⟩ := h491c
                        linarith only [h450, h487, hc01, hlam, hphi, ht12, p491_0, p491_1, p491_2, p491_3, u2e1]
                      · obtain ⟨p491_0, p491_1, p491_2, p491_3⟩ := h491c
                        linarith only [hc01, hc14, hlam, hphi, p491_0, p491_1, p491_2, p491_3]
                      · obtain ⟨p491_0, p491_1, p491_2, p491_3⟩ := h491c
                        linarith only [h488, hlam, p491_0, p491_1, p491_2, p491_3]
                      · obtain ⟨p491_0, p491_1, p491_2, p491_3⟩ := h491c
                        linarith only [h489, hlam, p491_0, p491_1, p491_2, p491_3]
                    · rcases h1bigk with h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c
                      · obtain ⟨p504_0, p504_1, p504_2, p504_3⟩ := h504c
                        linarith only [h0, hlam, p504_0, p504_1, p504_2, p504_3]
                      · obtain ⟨p504_0, p504_1, p504_2, p504_3⟩ := h504c
                        linarith only [h382, hlam, p504_0, p504_1, p504_2, p504_3]
                      · obtain ⟨p504_0, p504_1, p504_2, p504_3⟩ := h504c
                        linarith only [h450, hlam, p504_0, p504_1, p504_2, p504_3]
                      · obtain ⟨p504_0, p504_1, p504_2, p504_3⟩ := h504c
                        linarith only [hc01, hlam, hphi, ht12, p504_0, p504_1, p504_2, p504_3, u2e1]
                      · obtain ⟨p504_0, p504_1, p504_2, p504_3⟩ := h504c
                        linarith only [hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht4b, p504_0, p504_1, p504_2, p504_3, u2e1]
                      · obtain ⟨p504_0, p504_1, p504_2, p504_3⟩ := h504c
                        linarith only [h450, hc01, hlam, hphi, ht12, p504_0, p504_1, p504_2, p504_3, u2e1]
                      · obtain ⟨p504_0, p504_1, p504_2, p504_3⟩ := h504c
                        linarith only [hc01, hc13, hlam, hphi, p504_0, p504_1, p504_2, p504_3]
                      · obtain ⟨p504_0, p504_1, p504_2, p504_3⟩ := h504c
                        linarith only [h487, hlam, p504_0, p504_1, p504_2, p504_3]
                      · obtain ⟨p504_0, p504_1, p504_2, p504_3⟩ := h504c
                        linarith only [h450, h487, hc01, hlam, hphi, ht12, p504_0, p504_1, p504_2, p504_3, u2e1]
                      · obtain ⟨p504_0, p504_1, p504_2, p504_3⟩ := h504c
                        linarith only [hc01, hc14, hlam, hphi, p504_0, p504_1, p504_2, p504_3]
                      · obtain ⟨p504_0, p504_1, p504_2, p504_3⟩ := h504c
                        linarith only [h488, hlam, p504_0, p504_1, p504_2, p504_3]
                      · obtain ⟨p504_0, p504_1, p504_2, p504_3⟩ := h504c
                        linarith only [h489, hlam, p504_0, p504_1, p504_2, p504_3]
                  · linarith only [h382, h484, h486, h489, hc01, hlam, hphi, ht12, u2e0]
                · linarith only [h0, h488, hc01, hlam, hphi, ht12, u2e3]
              · linarith only [h0, h487, hc01, hlam, hphi, ht12, u2e2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h520 | h520
              · rcases m.htr 1 2 4 (by decide) (by decide) with h521 | h521
                · rcases m.htr 1 3 4 (by decide) (by decide) with h522 | h522
                  · linarith only [h382, h486, h520, h522, hc01, hlam, hphi, ht12, u2e1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h524 | h524
                    · linarith only [h382, h522, h524, hc01, hlam, hphi, ht12, u2e2]
                    · rcases h1bigk with h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c
                      · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                        linarith only [h0, hlam, p526_0, p526_1, p526_2, p526_3]
                      · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                        linarith only [h382, hlam, p526_0, p526_1, p526_2, p526_3]
                      · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                        linarith only [h450, hlam, p526_0, p526_1, p526_2, p526_3]
                      · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                        linarith only [hc01, hlam, hphi, ht12, p526_0, p526_1, p526_2, p526_3, u2e1]
                      · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                        linarith only [h382, hc01, hlam, hphi, ht12, p526_0, p526_1, p526_2, p526_3, u2e1]
                      · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                        linarith only [h382, h522, hc01, hlam, hphi, ht12, p526_0, p526_1, p526_2, p526_3, u2e1]
                      · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                        linarith only [hc01, hc13, hlam, hphi, p526_0, p526_1, p526_2, p526_3]
                      · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                        linarith only [h520, hlam, p526_0, p526_1, p526_2, p526_3]
                      · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                        linarith only [h522, hlam, p526_0, p526_1, p526_2, p526_3]
                      · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                        linarith only [hc01, hc14, hlam, hphi, p526_0, p526_1, p526_2, p526_3]
                      · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                        linarith only [h521, hlam, p526_0, p526_1, p526_2, p526_3]
                      · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                        linarith only [h521, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht4b, p526_0, p526_1, p526_2, p526_3, u2e1]
                · linarith only [h0, h485, h521, hlam]
              · linarith only [h0, h520, hc01, hlam, hphi, ht12, u2e2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h541 | h541
            · linarith only [h484, h485, h541, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h543 | h543
              · rcases m.htr 1 2 4 (by decide) (by decide) with h544 | h544
                · linarith only [h485, h544, hc02, hlam, hphi, u2e1]
                · linarith only [h0, h544, hc01, hlam, hphi, ht12, u2e3]
              · linarith only [h0, h484, h485, h543, hc01, hlam, hphi, ht12, u2e3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h548 | h548
          · rcases m.htr 0 3 4 (by decide) (by decide) with h549 | h549
            · rcases m.htr 1 2 3 (by decide) (by decide) with h550 | h550
              · linarith only [h484, h550, hc02, hlam, hphi, u2e1]
              · linarith only [h0, h550, hc01, hlam, hphi, ht12, u2e2]
            · linarith only [h484, h548, h549, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h554 | h554
            · rcases m.htr 1 2 3 (by decide) (by decide) with h555 | h555
              · linarith only [h484, h555, hc02, hlam, hphi, u2e1]
              · linarith only [h0, h555, hc01, hlam, hphi, ht12, u2e2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h558 | h558
              · linarith only [h484, h558, hc02, hlam, hphi, u2e1]
              · linarith only [h0, h558, hc01, hlam, hphi, ht12, u2e2]

end R2N4
