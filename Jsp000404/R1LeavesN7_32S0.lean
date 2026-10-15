import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
    · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
        · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
          · rcases h0bigk with h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [hlam, p12_0]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi0]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi3]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi0]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h0, hlam, p12_0]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [hlam, p12_0]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h11, h2, h7, hc02, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h0, h11, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h1, hlam, p12_1]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h4, hlam, p12_1]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [hlam, p12_0]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h11, h2, hc03, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h0, h4, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h2, hlam, p12_0]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h5, hlam, p12_0]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h7, hlam, p12_0]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [hlam, p12_0]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h3, hlam, p12_0]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h6, hlam, p12_1]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h8, hlam, p12_0]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [h9, hlam, p12_1]
            · have p12_0 := h12c.1
              have p12_1 := h12c.2.1
              have p12_2 := h12c.2.2.1
              have p12_3 := h12c.2.2.2
              linarith only [hlam, p12_0]
          · rcases h0bigk with h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [hlam, p38_0]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p38_1, u4ehi0]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p38_1, u4ehi0]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p38_1, u4ehi0]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h11, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p38_1, u4ehi1]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h0, hlam, p38_0]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [hlam, p38_0]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h2, h7, hc02, hlam, hphi, ht0b, ht45, ht5b, p38_1, u4ehi1]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p38_1, u4ehi1]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h0, h11, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p38_1, u4ehi1]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h1, hlam, p38_1]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h4, hlam, p38_1]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [hlam, p38_0]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h2, hc03, hlam, hphi, ht0b, ht45, ht5b, p38_1, u4ehi1]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h0, h11, h4, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p38_1, u4ehi1]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h2, hlam, p38_0]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h5, hlam, p38_0]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h7, hlam, p38_0]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [hlam, p38_0]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h11, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, p38_1, u4ehi1]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h3, hlam, p38_0]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h6, hlam, p38_1]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h8, hlam, p38_0]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [h9, hlam, p38_1]
            · have p38_0 := h38c.1
              have p38_1 := h38c.2.1
              have p38_2 := h38c.2.2.1
              have p38_3 := h38c.2.2.2
              linarith only [hlam, p38_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h64 | h64
          · rcases h0bigk with h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [hlam, p65_0]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p65_1, u4ehi0]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p65_1, u4ehi0]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p65_1, u4ehi0]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h3, h64, hc01, hlam, hphi, ht0b, ht45, ht5b, p65_1, u4ehi4]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h0, hlam, p65_0]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [hlam, p65_0]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h2, h64, h7, hc02, hlam, hphi, ht0b, ht45, ht5b, p65_1, u4ehi4]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h0, h2, h64, hc01, hlam, hphi, ht0b, ht45, ht5b, p65_1, u4ehi4]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h0, h3, h64, hc01, hlam, hphi, ht0b, ht45, ht5b, p65_1, u4ehi4]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h1, hlam, p65_1]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h4, hlam, p65_1]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [hlam, p65_0]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h2, h64, hc03, hlam, hphi, ht0b, ht45, ht5b, p65_1, u4ehi4]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h0, h3, h4, h64, hc01, hlam, hphi, ht0b, ht45, ht5b, p65_1, u4ehi4]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h2, hlam, p65_0]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h5, hlam, p65_0]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h7, hlam, p65_0]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [hlam, p65_0]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h3, h64, hc04, hlam, hphi, ht0b, ht45, ht5b, p65_1, u4ehi4]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h3, hlam, p65_0]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h6, hlam, p65_1]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h8, hlam, p65_0]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [h9, hlam, p65_1]
            · have p65_0 := h65c.1
              have p65_1 := h65c.2.1
              have p65_2 := h65c.2.2.1
              have p65_3 := h65c.2.2.2
              linarith only [hlam, p65_0]
          · rcases h0bigk with h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [hlam, p91_0]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p91_1, u4ehi0]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p91_1, u4ehi0]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p91_1, u4ehi0]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h64, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p91_1, u4ehi1]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h0, hlam, p91_0]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [hlam, p91_0]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h64, h7, h9, hc02, hlam, hphi, ht0b, ht45, ht5b, p91_1, u4ehi1]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h0, h64, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p91_1, u4ehi1]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h0, h64, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p91_1, u4ehi1]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h1, hlam, p91_1]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h4, hlam, p91_1]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [hlam, p91_0]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h64, h9, hc03, hlam, hphi, ht0b, ht45, ht5b, p91_1, u4ehi1]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h0, h4, h64, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p91_1, u4ehi1]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h2, hlam, p91_0]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h5, hlam, p91_0]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h7, hlam, p91_0]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [hlam, p91_0]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h0, h4, h64, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p91_1, u4ehi1]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h3, hlam, p91_0]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h6, hlam, p91_1]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h8, hlam, p91_0]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [h9, hlam, p91_1]
            · have p91_0 := h91c.1
              have p91_1 := h91c.2.1
              have p91_2 := h91c.2.2.1
              have p91_3 := h91c.2.2.2
              linarith only [hlam, p91_0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h117 | h117
        · rcases m.htr 1 4 5 (by decide) (by decide) with h118 | h118
          · linarith only [h118, h2, h9, hlam]
          · rcases h0bigk with h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p120_1]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p120_1, u4ehi3]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p120_1, u4ehi0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h2, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p120_1, u4ehi1]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h0, hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h7, hc02, hlam, hphi, ht0b, ht45, ht5b, p120_1, u4ehi3]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p120_1, u4ehi1]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h0, h2, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p120_1, u4ehi1]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h1, hlam, p120_1]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h4, hlam, p120_1]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h2, hc03, hlam, hphi, ht0b, ht45, ht5b, p120_1, u4ehi1]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h0, h2, h4, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p120_1, u4ehi1]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h2, hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h5, hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h7, hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h9, hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h3, hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h6, hlam, p120_1]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h8, hlam, p120_0]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [h2, hc05, hlam, hphi, ht0b, ht45, ht5b, p120_1, u4ehi1]
            · have p120_0 := h120c.1
              have p120_1 := h120c.2.1
              have p120_2 := h120c.2.2.1
              have p120_3 := h120c.2.2.2
              linarith only [hlam, p120_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h146 | h146
          · linarith only [h146, h2, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
          · rcases h0bigk with h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [hlam, p148_0]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h117, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p148_1]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h117, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p148_1]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p148_1, u4ehi1]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h2, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p148_1, u4ehi1]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h0, hlam, p148_0]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [hlam, p148_0]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h7, hc02, hlam, hphi, ht0b, ht45, ht5b, p148_1, u4ehi3]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p148_1, u4ehi1]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h0, h2, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p148_1, u4ehi1]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h1, hlam, p148_1]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h4, hlam, p148_1]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [hlam, p148_0]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h2, hc03, hlam, hphi, ht0b, ht45, ht5b, p148_1, u4ehi1]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h0, h2, h4, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p148_1, u4ehi1]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h2, hlam, p148_0]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h5, hlam, p148_0]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h7, hlam, p148_0]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [hlam, p148_0]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h9, hlam, p148_0]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h3, hlam, p148_0]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h6, hlam, p148_1]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h8, hlam, p148_0]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [h2, hc05, hlam, hphi, ht0b, ht45, ht5b, p148_1, u4ehi1]
            · have p148_0 := h148c.1
              have p148_1 := h148c.2.1
              have p148_2 := h148c.2.2.1
              have p148_3 := h148c.2.2.2
              linarith only [hlam, p148_0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h174 | h174
      · linarith only [h174, h7, h8, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h176 | h176
        · rcases m.htr 1 4 5 (by decide) (by decide) with h177 | h177
          · linarith only [h174, h177, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
          · rcases h0bigk with h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [hlam, p179_0]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h0, h176, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p179_1]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p179_1, u4ehi3]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p179_1, u4ehi1]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h7, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p179_1, u4ehi3]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h0, hlam, p179_0]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [hlam, p179_0]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h7, hc02, hlam, hphi, ht0b, ht45, ht5b, p179_1, u4ehi3]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p179_1, u4ehi1]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h0, h7, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p179_1, u4ehi3]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h1, hlam, p179_1]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h4, hlam, p179_1]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [hlam, p179_0]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h2, hc03, hlam, hphi, ht0b, ht45, ht5b, p179_1, u4ehi1]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h8, hlam, p179_1]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h2, hlam, p179_0]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h5, hlam, p179_0]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h7, hlam, p179_0]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [hlam, p179_0]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h174, hlam, p179_0]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h3, hlam, p179_0]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h6, hlam, p179_1]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h174, hc03, hc45, hlam, hphi, ht34, p179_1]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [h174, h2, hc45, hlam, hphi, p179_1, u4ehi1]
            · have p179_0 := h179c.1
              have p179_1 := h179c.2.1
              have p179_2 := h179c.2.2.1
              have p179_3 := h179c.2.2.2
              linarith only [hlam, p179_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h205 | h205
          · linarith only [h174, h2, h205, h7, h8, hlam]
          · rcases h0bigk with h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [hlam, p207_0]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p207_1]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p207_1, u4ehi0]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p207_1, u4ehi1]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h2, h7, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p207_1, u4ehi1]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h0, hlam, p207_0]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [hlam, p207_0]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h2, h7, hc02, hlam, hphi, ht0b, ht45, ht5b, p207_1, u4ehi1]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p207_1, u4ehi1]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h0, h176, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h1, hlam, p207_1]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h4, hlam, p207_1]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [hlam, p207_0]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h2, hc03, hlam, hphi, ht0b, ht45, ht5b, p207_1, u4ehi1]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h8, hlam, p207_1]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h2, hlam, p207_0]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h5, hlam, p207_0]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h7, hlam, p207_0]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [hlam, p207_0]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h174, hlam, p207_0]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h3, hlam, p207_0]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h6, hlam, p207_1]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h176, h3, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [h174, h2, hc45, hlam, hphi, p207_1, u4ehi1]
            · have p207_0 := h207c.1
              have p207_1 := h207c.2.1
              have p207_2 := h207c.2.2.1
              have p207_3 := h207c.2.2.2
              linarith only [hlam, p207_0]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h233 | h233
    · rcases m.htr 0 4 5 (by decide) (by decide) with h234 | h234
      · rcases m.htr 1 2 3 (by decide) (by decide) with h235 | h235
        · rcases m.htr 1 4 5 (by decide) (by decide) with h236 | h236
          · rcases h0bigk with h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [hlam, p237_0]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h0, h235, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p237_1]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h233, hc01, hc35, hlam, hphi, ht0b, ht5b, p237_1]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h2, h236, hc01, hlam, hphi, ht0b, ht45, ht5b, p237_1, u4ehi4]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h234, hc01, hlam, hphi, ht0b, ht45, ht5b, p237_1, u4ehi4]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h0, hlam, p237_0]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [hlam, p237_0]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h233, hc02, hc35, hlam, hphi, ht0b, ht5b, p237_1]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h0, h2, h236, hc01, hlam, hphi, ht0b, ht45, ht5b, p237_1, u4ehi4]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h0, h234, hc01, hlam, hphi, ht0b, ht45, ht5b, p237_1, u4ehi4]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h1, hlam, p237_1]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h4, hlam, p237_1]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [hlam, p237_0]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h7, hlam, p237_1]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h7, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p237_1]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h2, hlam, p237_0]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h5, hlam, p237_0]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h1, h7, hc13, hc34, hlam, hphi, p237_1]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [hlam, p237_0]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h234, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p237_1, u4ehi4]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h3, hlam, p237_0]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h6, hlam, p237_1]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h233, hlam, p237_0]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [h234, hlam, p237_1]
            · have p237_0 := h237c.1
              have p237_1 := h237c.2.1
              have p237_2 := h237c.2.2.1
              have p237_3 := h237c.2.2.2
              linarith only [hlam, p237_0]
          · rcases h0bigk with h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [hlam, p263_0]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h0, h235, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p263_1]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h233, h234, h236, hc01, hlam, hphi, ht0b, ht45, ht5b, p263_1, u4ehi1]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p263_1, u4ehi0]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h234, h236, hc01, hlam, hphi, ht0b, ht45, ht5b, p263_1, u4ehi1]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h0, hlam, p263_0]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [hlam, p263_0]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h233, h234, h236, hc02, hlam, hphi, ht0b, ht45, ht5b, p263_1, u4ehi1]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p263_1, u4ehi1]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h0, h234, h236, hc01, hlam, hphi, ht0b, ht45, ht5b, p263_1, u4ehi1]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h1, hlam, p263_1]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h4, hlam, p263_1]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [hlam, p263_0]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h7, hlam, p263_1]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h234, h236, hc03, hlam, hphi, ht0b, ht45, ht5b, p263_1, u4ehi1]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h2, hlam, p263_0]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h5, hlam, p263_0]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h1, h235, h7, hc23, hc34, hlam, hphi, p263_1]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [hlam, p263_0]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h234, h236, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p263_1, u4ehi1]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h3, hlam, p263_0]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h6, hlam, p263_1]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h233, hlam, p263_0]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [h234, hlam, p263_1]
            · have p263_0 := h263c.1
              have p263_1 := h263c.2.1
              have p263_2 := h263c.2.2.1
              have p263_3 := h263c.2.2.2
              linarith only [hlam, p263_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h289 | h289
          · rcases h0bigk with h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [hlam, p290_0]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h235, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p290_1]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h235, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p290_1]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p290_1, u4ehi0]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h289, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p290_1, u4ehi4]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h0, hlam, p290_0]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [hlam, p290_0]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h235, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p290_1]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h0, h2, h289, hc01, hlam, hphi, ht0b, ht45, ht5b, p290_1, u4ehi4]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h0, h289, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p290_1, u4ehi4]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h1, hlam, p290_1]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h4, hlam, p290_1]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [hlam, p290_0]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h7, hlam, p290_1]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h289, h3, hc03, hlam, hphi, ht0b, ht45, ht5b, p290_1, u4ehi4]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h2, hlam, p290_0]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h5, hlam, p290_0]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h2, h235, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p290_1]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [hlam, p290_0]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h289, h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p290_1, u4ehi4]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h3, hlam, p290_0]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h6, hlam, p290_1]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h233, hlam, p290_0]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [h234, hlam, p290_1]
            · have p290_0 := h290c.1
              have p290_1 := h290c.2.1
              have p290_2 := h290c.2.2.1
              have p290_3 := h290c.2.2.2
              linarith only [hlam, p290_0]
          · rcases h0bigk with h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [hlam, p316_0]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h235, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p316_1]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h235, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p316_1]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p316_1, u4ehi0]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h234, h289, hc01, hlam, hphi, ht0b, ht45, ht5b, p316_1, u4ehi1]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h0, hlam, p316_0]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [hlam, p316_0]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h234, h235, h289, h4, h7, hc02, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p316_1, u4ehi1]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h0, h234, h289, hc01, hlam, hphi, ht0b, ht45, ht5b, p316_1, u4ehi1]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h0, h234, h289, hc01, hlam, hphi, ht0b, ht45, ht5b, p316_1, u4ehi1]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h1, hlam, p316_1]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h4, hlam, p316_1]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [hlam, p316_0]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h7, hlam, p316_1]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h7, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p316_1]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h2, hlam, p316_0]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h5, hlam, p316_0]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h0, h235, h4, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p316_1]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [hlam, p316_0]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h234, h289, hc04, hlam, hphi, ht0b, ht45, ht5b, p316_1, u4ehi1]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h3, hlam, p316_0]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h6, hlam, p316_1]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h233, hlam, p316_0]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [h234, hlam, p316_1]
            · have p316_0 := h316c.1
              have p316_1 := h316c.2.1
              have p316_2 := h316c.2.2.1
              have p316_3 := h316c.2.2.2
              linarith only [hlam, p316_0]
      · linarith only [h233, h234, h7, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h343 | h343
      · rcases m.htr 1 2 3 (by decide) (by decide) with h344 | h344
        · rcases m.htr 1 4 5 (by decide) (by decide) with h345 | h345
          · rcases h0bigk with h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [hlam, p346_0]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h0, h344, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p346_1]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              rcases p346_3 (m.d 0 1) (by simp) with h349 | h349
              · rcases p346_3 (m.d 0 2) (by simp) with h350 | h350
                · linarith only [h0, h350, hlam]
                · linarith only [h350, h4, hlam]
              · linarith only [h1, h349, hlam]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h2, h345, hc01, hlam, hphi, ht0b, ht45, ht5b, p346_1, u4ehi4]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h3, h345, hc01, hlam, hphi, ht0b, ht45, ht5b, p346_1, u4ehi4]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h0, hlam, p346_0]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [hlam, p346_0]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              rcases p346_3 (m.d 0 1) (by simp) with h358 | h358
              · rcases p346_3 (m.d 0 2) (by simp) with h359 | h359
                · rcases p346_3 (m.d 0 3) (by simp) with h360 | h360
                  · linarith only [h360, h4, hlam]
                  · rcases p346_3 (m.d 0 4) (by simp) with h362 | h362
                    · linarith only [h362, h5, hlam]
                    · linarith only [h362, h7, hlam]
                · linarith only [h359, h4, hlam]
              · linarith only [h1, h358, hlam]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h2, h345, hc02, hlam, hphi, ht0b, ht45, ht5b, p346_1, u4ehi4]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h0, h3, h345, hc01, hlam, hphi, ht0b, ht45, ht5b, p346_1, u4ehi4]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h1, hlam, p346_1]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h4, hlam, p346_1]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [hlam, p346_0]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h7, hlam, p346_1]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h233, hlam, p346_1]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h2, hlam, p346_0]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h5, hlam, p346_0]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h1, h344, h7, hc23, hc34, hlam, hphi, p346_1]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [hlam, p346_0]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h3, h345, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p346_1, u4ehi4]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h3, hlam, p346_0]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h6, hlam, p346_1]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h1, h233, h344, hc23, hc35, hlam, hphi, p346_1]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [h343, hlam, p346_1]
            · have p346_0 := h346c.1
              have p346_1 := h346c.2.1
              have p346_2 := h346c.2.2.1
              have p346_3 := h346c.2.2.2
              linarith only [hlam, p346_0]
          · rcases h0bigk with h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p384_1, u4ehi0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              rcases p384_3 (m.d 0 1) (by simp) with h387 | h387
              · rcases p384_3 (m.d 0 2) (by simp) with h388 | h388
                · linarith only [h0, h388, hlam]
                · linarith only [h388, h4, hlam]
              · linarith only [h1, h387, hlam]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h343, h345, hc01, hlam, hphi, ht0b, ht45, ht5b, p384_1, u4ehi1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h343, h345, hc01, hlam, hphi, ht0b, ht45, ht5b, p384_1, u4ehi1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h0, hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              rcases p384_3 (m.d 0 1) (by simp) with h396 | h396
              · rcases p384_3 (m.d 0 2) (by simp) with h397 | h397
                · rcases p384_3 (m.d 0 3) (by simp) with h398 | h398
                  · linarith only [h398, h4, hlam]
                  · rcases p384_3 (m.d 0 4) (by simp) with h400 | h400
                    · linarith only [h400, h5, hlam]
                    · linarith only [h400, h7, hlam]
                · linarith only [h397, h4, hlam]
              · linarith only [h1, h396, hlam]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h343, h345, hc02, hlam, hphi, ht0b, ht45, ht5b, p384_1, u4ehi1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h0, h343, h345, hc01, hlam, hphi, ht0b, ht45, ht5b, p384_1, u4ehi1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h1, hlam, p384_1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h4, hlam, p384_1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h7, hlam, p384_1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h233, hlam, p384_1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h2, hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h5, hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h1, h344, h7, hc23, hc34, hlam, hphi, p384_1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h343, h345, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p384_1, u4ehi1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h3, hlam, p384_0]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h6, hlam, p384_1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h1, h233, h344, hc23, hc35, hlam, hphi, p384_1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [h343, hlam, p384_1]
            · have p384_0 := h384c.1
              have p384_1 := h384c.2.1
              have p384_2 := h384c.2.2.1
              have p384_3 := h384c.2.2.2
              linarith only [hlam, p384_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h422 | h422
          · rcases h0bigk with h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [hlam, p423_0]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h344, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p423_1]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h344, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p423_1]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p423_1, u4ehi0]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h233, h344, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p423_1]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h0, hlam, p423_0]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [hlam, p423_0]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h344, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p423_1]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h0, h2, h422, hc01, hlam, hphi, ht0b, ht45, ht5b, p423_1, u4ehi4]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h0, h233, h344, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p423_1]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h1, hlam, p423_1]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h4, hlam, p423_1]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [hlam, p423_0]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h7, hlam, p423_1]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h233, hlam, p423_1]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h2, hlam, p423_0]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h5, hlam, p423_0]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h344, h4, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p423_1]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [hlam, p423_0]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h233, h344, h4, h7, hc12, hc34, hlam, hphi, ht23, p423_1]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h3, hlam, p423_0]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h6, hlam, p423_1]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h344, h4, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p423_1]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [h343, hlam, p423_1]
            · have p423_0 := h423c.1
              have p423_1 := h423c.2.1
              have p423_2 := h423c.2.2.1
              have p423_3 := h423c.2.2.2
              linarith only [hlam, p423_0]
          · rcases h0bigk with h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [hlam, p449_0]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h343, h344, h4, h422, h7, hc01, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p449_1, u4ehi1]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h343, h344, h4, h422, h7, hc01, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p449_1, u4ehi1]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h343, h422, hc01, hlam, hphi, ht0b, ht45, ht5b, p449_1, u4ehi1]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h233, h343, h344, h4, h422, h7, hc01, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p449_1, u4ehi1]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h0, hlam, p449_0]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [hlam, p449_0]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h343, h344, h4, h422, h7, hc02, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p449_1, u4ehi1]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h0, h343, h422, hc01, hlam, hphi, ht0b, ht45, ht5b, p449_1, u4ehi1]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h0, h233, h343, h344, h4, h422, h7, hc01, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p449_1, u4ehi1]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h1, hlam, p449_1]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h4, hlam, p449_1]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [hlam, p449_0]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h7, hlam, p449_1]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h233, hlam, p449_1]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h2, hlam, p449_0]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h5, hlam, p449_0]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h344, h4, h7, hc12, hc34, hlam, hphi, ht23, p449_1]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [hlam, p449_0]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h233, h344, h4, h7, hc12, hc34, hlam, hphi, ht23, p449_1]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h3, hlam, p449_0]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h6, hlam, p449_1]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h343, h344, h4, h422, h7, hc05, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p449_1, u4ehi1]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [h343, hlam, p449_1]
            · have p449_0 := h449c.1
              have p449_1 := h449c.2.1
              have p449_2 := h449c.2.2.1
              have p449_3 := h449c.2.2.2
              linarith only [hlam, p449_0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h475 | h475
        · rcases m.htr 1 4 5 (by decide) (by decide) with h476 | h476
          · linarith only [h2, h343, h476, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
          · rcases h0bigk with h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [hlam, p478_0]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h0, h475, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p478_1]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              rcases p478_3 (m.d 0 1) (by simp) with h481 | h481
              · rcases p478_3 (m.d 0 2) (by simp) with h482 | h482
                · linarith only [h0, h482, hlam]
                · linarith only [h4, h482, hlam]
              · linarith only [h1, h481, hlam]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p478_1, u4ehi1]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h2, h343, hc01, hlam, hphi, ht0b, ht45, ht5b, p478_1, u4ehi1]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h0, hlam, p478_0]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [hlam, p478_0]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              rcases p478_3 (m.d 0 1) (by simp) with h490 | h490
              · rcases p478_3 (m.d 0 2) (by simp) with h491 | h491
                · rcases p478_3 (m.d 0 3) (by simp) with h492 | h492
                  · linarith only [h4, h492, hlam]
                  · rcases p478_3 (m.d 0 4) (by simp) with h494 | h494
                    · linarith only [h494, h5, hlam]
                    · linarith only [h494, h7, hlam]
                · linarith only [h4, h491, hlam]
              · linarith only [h1, h490, hlam]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p478_1, u4ehi1]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h0, h2, h343, hc01, hlam, hphi, ht0b, ht45, ht5b, p478_1, u4ehi1]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h1, hlam, p478_1]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h4, hlam, p478_1]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [hlam, p478_0]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h7, hlam, p478_1]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h233, hlam, p478_1]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h2, hlam, p478_0]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h5, hlam, p478_0]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h1, h343, hc13, hc45, hlam, hphi, ht34, p478_1]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [hlam, p478_0]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h343, hlam, p478_0]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h3, hlam, p478_0]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h6, hlam, p478_1]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h1, h233, hc13, hc35, hlam, hphi, p478_1]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [h343, hc45, hlam, hphi, p478_1, u4ehi0]
            · have p478_0 := h478c.1
              have p478_1 := h478c.2.1
              have p478_2 := h478c.2.2.1
              have p478_3 := h478c.2.2.2
              linarith only [hlam, p478_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h516 | h516
          · linarith only [h2, h343, h516, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
          · rcases h0bigk with h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [hlam, p518_0]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h4, h475, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p518_1]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h4, h475, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p518_1]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h4, h475, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p518_1]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h233, h4, h475, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p518_1]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h0, hlam, p518_0]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [hlam, p518_0]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h4, h475, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p518_1]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h0, h4, h475, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p518_1]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h0, h233, h4, h475, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p518_1]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h1, hlam, p518_1]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h4, hlam, p518_1]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [hlam, p518_0]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h7, hlam, p518_1]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h233, hlam, p518_1]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h2, hlam, p518_0]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h5, hlam, p518_0]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h4, h475, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p518_1]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [hlam, p518_0]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h343, hlam, p518_0]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h3, hlam, p518_0]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h6, hlam, p518_1]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h4, h475, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p518_1]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [h343, hc45, hlam, hphi, p518_1, u4ehi0]
            · have p518_0 := h518c.1
              have p518_1 := h518c.2.1
              have p518_2 := h518c.2.2.1
              have p518_3 := h518c.2.2.2
              linarith only [hlam, p518_0]

end R2N4
