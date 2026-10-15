import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
      · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
            · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
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
                  linarith only [h11, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p12_1, u3ehi3]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p12_1, u3ehi0]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p12_1]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p12_1, u3ehi4]
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
                  linarith only [h11, h4, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p12_1, u3ehi3]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p12_1, u3ehi3]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p12_1, u3ehi4]
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
                  linarith only [h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p12_1, u3ehi3]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p12_1, u3ehi4]
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
                  linarith only [h8, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p12_1, u3ehi4]
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
                  linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p38_1, u3ehi0]
                · have p38_0 := h38c.1
                  have p38_1 := h38c.2.1
                  have p38_2 := h38c.2.2.1
                  have p38_3 := h38c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p38_1, u3ehi0]
                · have p38_0 := h38c.1
                  have p38_1 := h38c.2.1
                  have p38_2 := h38c.2.2.1
                  have p38_3 := h38c.2.2.2
                  linarith only [h11, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p38_1, u3ehi2]
                · have p38_0 := h38c.1
                  have p38_1 := h38c.2.1
                  have p38_2 := h38c.2.2.1
                  have p38_3 := h38c.2.2.2
                  linarith only [h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p38_1, u3ehi4]
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
                  linarith only [h11, h7, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p38_1, u3ehi2]
                · have p38_0 := h38c.1
                  have p38_1 := h38c.2.1
                  have p38_2 := h38c.2.2.1
                  have p38_3 := h38c.2.2.2
                  linarith only [h0, h11, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p38_1, u3ehi2]
                · have p38_0 := h38c.1
                  have p38_1 := h38c.2.1
                  have p38_2 := h38c.2.2.1
                  have p38_3 := h38c.2.2.2
                  linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p38_1, u3ehi4]
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
                  linarith only [h0, h11, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p38_1, u3ehi2]
                · have p38_0 := h38c.1
                  have p38_1 := h38c.2.1
                  have p38_2 := h38c.2.2.1
                  have p38_3 := h38c.2.2.2
                  linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p38_1, u3ehi4]
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
                  linarith only [h8, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p38_1, u3ehi4]
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
            · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
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
                  linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p65_1, u3ehi0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p65_1, u3ehi0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h10, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p65_1]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p65_1, u3ehi4]
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
                  linarith only [h4, h64, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p65_1, u3ehi3]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h0, h10, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p65_1]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p65_1, u3ehi4]
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
                  linarith only [h10, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p65_1]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p65_1, u3ehi4]
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
                  linarith only [h8, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p65_1, u3ehi4]
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
                  linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1, u3ehi0]
                · have p91_0 := h91c.1
                  have p91_1 := h91c.2.1
                  have p91_2 := h91c.2.2.1
                  have p91_3 := h91c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1, u3ehi0]
                · have p91_0 := h91c.1
                  have p91_1 := h91c.2.1
                  have p91_2 := h91c.2.2.1
                  have p91_3 := h91c.2.2.2
                  linarith only [h10, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p91_1]
                · have p91_0 := h91c.1
                  have p91_1 := h91c.2.1
                  have p91_2 := h91c.2.2.1
                  have p91_3 := h91c.2.2.2
                  linarith only [h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1, u3ehi4]
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
                  linarith only [h1, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1, u3ehi1]
                · have p91_0 := h91c.1
                  have p91_1 := h91c.2.1
                  have p91_2 := h91c.2.2.1
                  have p91_3 := h91c.2.2.2
                  linarith only [h0, h10, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p91_1]
                · have p91_0 := h91c.1
                  have p91_1 := h91c.2.1
                  have p91_2 := h91c.2.2.1
                  have p91_3 := h91c.2.2.2
                  linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1, u3ehi4]
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
                  linarith only [h10, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p91_1]
                · have p91_0 := h91c.1
                  have p91_1 := h91c.2.1
                  have p91_2 := h91c.2.2.1
                  have p91_3 := h91c.2.2.2
                  linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1, u3ehi4]
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
                  linarith only [h8, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1, u3ehi4]
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
          · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
            · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
              · rcases h0bigk with h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [hlam, p119_0]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p119_1, u3ehi0]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p119_1, u3ehi0]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h118, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p119_1, u3ehi3]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h118, h5, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p119_1, u3ehi3]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h0, hlam, p119_0]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [hlam, p119_0]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h1, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p119_1, u3ehi1]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h0, h118, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p119_1, u3ehi3]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h0, h118, h5, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p119_1, u3ehi3]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h1, hlam, p119_1]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h4, hlam, p119_1]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [hlam, p119_0]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h118, h5, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p119_1, u3ehi3]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h0, h118, h4, h5, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p119_1, u3ehi3]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h2, hlam, p119_0]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h5, hlam, p119_0]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h7, hlam, p119_0]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [hlam, p119_0]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h9, hlam, p119_0]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h3, hlam, p119_0]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h6, hlam, p119_1]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h8, hlam, p119_0]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [h118, h5, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p119_1, u3ehi3]
                · have p119_0 := h119c.1
                  have p119_1 := h119c.2.1
                  have p119_2 := h119c.2.2.1
                  have p119_3 := h119c.2.2.2
                  linarith only [hlam, p119_0]
              · linarith only [h118, h7, h9, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h146 | h146
              · rcases h0bigk with h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [hlam, p147_0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p147_1, u3ehi0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p147_1, u3ehi0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h117, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p147_1]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p147_1, u3ehi4]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h0, hlam, p147_0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [hlam, p147_0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h146, h4, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p147_1, u3ehi3]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h0, h117, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p147_1]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p147_1, u3ehi4]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h1, hlam, p147_1]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h4, hlam, p147_1]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [hlam, p147_0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h117, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p147_1]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p147_1, u3ehi4]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h2, hlam, p147_0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h5, hlam, p147_0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h7, hlam, p147_0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [hlam, p147_0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h9, hlam, p147_0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h3, hlam, p147_0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h6, hlam, p147_1]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h8, hlam, p147_0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h117, h5, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p147_1]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [hlam, p147_0]
              · linarith only [h146, h7, h9, hc45, hlam, hphi, ht34, u3ehi2]
        · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h175 | h175
        · linarith only [h175, h7, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h177 | h177
          · rcases m.htr 1 2 4 (by decide) (by decide) with h178 | h178
            · rcases m.htr 2 3 4 (by decide) (by decide) with h179 | h179
              · linarith only [h0, h179, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
              · rcases h0bigk with h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [hlam, p181_0]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h0, h178, h179, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p181_1, u3ehi2]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p181_1, u3ehi1]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h177, hc01, hc45, hlam, hphi, ht0b, ht5b, p181_1]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h1, h175, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p181_1, u3ehi1]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h0, hlam, p181_0]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [hlam, p181_0]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h1, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p181_1, u3ehi1]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h0, h178, h179, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p181_1, u3ehi2]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h0, h1, h175, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p181_1, u3ehi1]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h1, hlam, p181_1]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h4, hlam, p181_1]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [hlam, p181_0]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h7, hlam, p181_1]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h175, hlam, p181_1]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h2, hlam, p181_0]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h5, hlam, p181_0]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h1, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p181_1, u3ehi1]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [hlam, p181_0]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h1, h175, h7, hc34, hlam, hphi, p181_1, u3ehi1]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h3, hlam, p181_0]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h6, hlam, p181_1]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h1, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p181_1, u3ehi1]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [h177, hlam, p181_1]
                · have p181_0 := h181c.1
                  have p181_1 := h181c.2.1
                  have p181_2 := h181c.2.2.1
                  have p181_3 := h181c.2.2.2
                  linarith only [hlam, p181_0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h207 | h207
              · linarith only [h207, h4, h7, hlam]
              · rcases h0bigk with h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [hlam, p209_0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p209_1, u3ehi2]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p209_1, u3ehi0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h178, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p209_1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h1, h175, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p209_1, u3ehi1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h0, hlam, p209_0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [hlam, p209_0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h1, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p209_1, u3ehi1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h0, h178, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p209_1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h0, h1, h175, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p209_1, u3ehi1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h1, hlam, p209_1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h4, hlam, p209_1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [hlam, p209_0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h7, hlam, p209_1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h175, hlam, p209_1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h2, hlam, p209_0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h5, hlam, p209_0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h1, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p209_1, u3ehi1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [hlam, p209_0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h1, h175, h7, hc34, hlam, hphi, p209_1, u3ehi1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h3, hlam, p209_0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h6, hlam, p209_1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h1, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p209_1, u3ehi1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h177, hlam, p209_1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [hlam, p209_0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h235 | h235
            · rcases m.htr 2 3 4 (by decide) (by decide) with h236 | h236
              · linarith only [h236, h4, h7, hlam]
              · rcases h0bigk with h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [hlam, p238_0]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p238_1]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p238_1, u3ehi0]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h2, h235, h236, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p238_1, u3ehi2]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h1, h175, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p238_1, u3ehi1]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h0, hlam, p238_0]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [hlam, p238_0]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h1, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p238_1, u3ehi1]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h0, h2, h235, h236, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p238_1, u3ehi2]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h0, h1, h175, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p238_1, u3ehi1]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h1, hlam, p238_1]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h4, hlam, p238_1]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [hlam, p238_0]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h7, hlam, p238_1]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h175, hlam, p238_1]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h2, hlam, p238_0]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h5, hlam, p238_0]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h1, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p238_1, u3ehi1]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [hlam, p238_0]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h177, hlam, p238_0]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h3, hlam, p238_0]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h6, hlam, p238_1]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h1, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p238_1, u3ehi1]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [h177, hc04, hc45, hlam, hphi, p238_1]
                · have p238_0 := h238c.1
                  have p238_1 := h238c.2.1
                  have p238_2 := h238c.2.2.1
                  have p238_3 := h238c.2.2.2
                  linarith only [hlam, p238_0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h264 | h264
              · linarith only [h264, h4, h7, hlam]
              · rcases h0bigk with h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [hlam, p266_0]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p266_1, u3ehi2]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p266_1, u3ehi0]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h1, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p266_1, u3ehi1]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h1, h175, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p266_1, u3ehi1]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h0, hlam, p266_0]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [hlam, p266_0]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h1, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p266_1, u3ehi1]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h0, h1, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p266_1, u3ehi1]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h0, h1, h175, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p266_1, u3ehi1]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h1, hlam, p266_1]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h4, hlam, p266_1]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [hlam, p266_0]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h7, hlam, p266_1]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h175, hlam, p266_1]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h2, hlam, p266_0]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h5, hlam, p266_0]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h1, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p266_1, u3ehi1]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [hlam, p266_0]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h177, hlam, p266_0]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h3, hlam, p266_0]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h6, hlam, p266_1]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h1, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p266_1, u3ehi1]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [h177, hc04, hc45, hlam, hphi, p266_1]
                · have p266_0 := h266c.1
                  have p266_1 := h266c.2.1
                  have p266_2 := h266c.2.2.1
                  have p266_3 := h266c.2.2.2
                  linarith only [hlam, p266_0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h292 | h292
      · rcases m.htr 0 3 5 (by decide) (by decide) with h293 | h293
        · linarith only [h293, h4, h6, hlam]
        · linarith only [h292, h293, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h296 | h296
        · linarith only [h292, h296, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h298 | h298
          · linarith only [h298, h5, h6, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h300 | h300
            · rcases m.htr 2 3 4 (by decide) (by decide) with h301 | h301
              · linarith only [h301, h4, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · rcases h0bigk with h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [hlam, p303_0]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h0, h300, h301, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p303_1, u3ehi2]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p303_1, u3ehi0]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h301, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p303_1, u3ehi2]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h0, h300, h301, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p303_1, u3ehi2]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h0, hlam, p303_0]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [hlam, p303_0]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h1, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p303_1, u3ehi1]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h6, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p303_1]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h6, hlam, p303_0]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h1, hlam, p303_1]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h4, hlam, p303_1]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [hlam, p303_0]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h292, hlam, p303_1]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h296, hlam, p303_1]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h2, hlam, p303_0]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h5, hlam, p303_0]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h1, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p303_1, u3ehi1]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [hlam, p303_0]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h298, hlam, p303_0]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h3, hlam, p303_0]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h0, h300, h301, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p303_1, u3ehi2]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h1, h296, hc35, hlam, hphi, p303_1, u3ehi1]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [h298, hc04, hc45, hlam, hphi, p303_1]
                · have p303_0 := h303c.1
                  have p303_1 := h303c.2.1
                  have p303_2 := h303c.2.2.1
                  have p303_3 := h303c.2.2.2
                  linarith only [hlam, p303_0]
            · linarith only [h300, h5, h6, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h330 | h330
    · rcases m.htr 0 3 4 (by decide) (by decide) with h331 | h331
      · linarith only [h331, h4, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h333 | h333
        · linarith only [h331, h333, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h335 | h335
          · rcases m.htr 1 2 4 (by decide) (by decide) with h336 | h336
            · linarith only [h0, h330, h336, h5, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h338 | h338
              · linarith only [h338, h4, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h338, h4, h5, hc34, hlam, hphi, u3ehi2]
          · linarith only [h335, h4, h5, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h342 | h342
      · linarith only [h342, h4, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h344 | h344
        · linarith only [h342, h344, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h346 | h346
          · rcases m.htr 1 2 4 (by decide) (by decide) with h347 | h347
            · linarith only [h0, h347, h5, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h349 | h349
              · linarith only [h342, h349, h4, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
              · linarith only [h349, h4, h5, hc34, hlam, hphi, u3ehi2]
          · linarith only [h346, h4, h5, hc45, hlam, hphi, ht34, u3ehi2]

end R2N4
