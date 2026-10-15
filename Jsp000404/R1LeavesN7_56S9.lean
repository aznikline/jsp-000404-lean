import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4238000 in
set_option maxHeartbeats 4238000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
      · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
        · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
            · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
              · rcases h0bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h3, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi4]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi4]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h3, h9, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi4]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi3]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi4]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h1, hlam, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h3, hlam, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h6, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi3]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h3, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi4]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h3, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h4, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h6, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h3, h5, h6, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi4]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h2, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h5, hlam, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h7, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h8, hlam, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
              · rcases h0bigk with h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [hlam, p36_0]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi0]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi0]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi3]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi2]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h0, hlam, p36_0]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [hlam, p36_0]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h7, h9, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi2]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi3]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h0, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi2]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h1, hlam, p36_1]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h3, hlam, p36_1]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [hlam, p36_0]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h6, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi3]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h0, h3, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi2]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h0, h3, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi0]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h4, hlam, p36_0]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h6, hlam, p36_0]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [hlam, p36_0]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h0, h3, h6, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi2]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h2, hlam, p36_0]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h5, hlam, p36_1]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h7, hlam, p36_0]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h8, hlam, p36_1]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [hlam, p36_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h62 | h62
              · rcases h0bigk with h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi3]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi3]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h3, h62, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi4]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi3]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi3]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h1, hlam, p63_1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h3, hlam, p63_1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h6, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi3]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, h3, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi3]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, h3, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h4, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h6, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h8, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h2, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h5, hlam, p63_1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h7, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, h5, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi3]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
              · rcases h0bigk with h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1, u3ehi0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1, u3ehi0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1, u3ehi3]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h62, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1, u3ehi2]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h0, hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h62, h7, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1, u3ehi2]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1, u3ehi3]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h0, h62, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1, u3ehi2]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h1, hlam, p89_1]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h3, hlam, p89_1]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h6, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1, u3ehi3]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h0, h3, h62, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1, u3ehi2]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h0, h3, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1, u3ehi0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h4, hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h6, hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h8, hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h2, hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h5, hlam, p89_1]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h7, hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h6, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1, u3ehi3]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [hlam, p89_0]
          · linarith only [h6, h7, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h116 | h116
          · linarith only [h116, h6, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h118 | h118
            · rcases m.htr 2 3 5 (by decide) (by decide) with h119 | h119
              · linarith only [h0, h116, h119, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
              · rcases h0bigk with h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [hlam, p121_0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p121_1, u3ehi1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h118, hc01, hc45, hlam, hphi, ht0b, ht5b, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h119, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p121_1, u3ehi2]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h0, hlam, p121_0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [hlam, p121_0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h1, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p121_1, u3ehi1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h0, h118, hc01, hc45, hlam, hphi, ht0b, ht5b, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h0, h119, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p121_1, u3ehi2]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h1, hlam, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h3, hlam, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [hlam, p121_0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h6, hlam, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h116, hlam, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h4, hlam, p121_0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h0, h1, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p121_1, u3ehi1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [hlam, p121_0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h119, h5, h6, hc34, hlam, hphi, p121_1, u3ehi2]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h2, hlam, p121_0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h5, hlam, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h1, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p121_1, u3ehi1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h118, hlam, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [hlam, p121_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h147 | h147
              · linarith only [h147, h3, h6, hc34, hlam, hphi, u3ehi4]
              · rcases h0bigk with h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [hlam, p149_0]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p149_1, u3ehi2]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p149_1, u3ehi0]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h1, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p149_1, u3ehi1]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h147, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p149_1, u3ehi2]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h0, hlam, p149_0]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [hlam, p149_0]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h1, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p149_1, u3ehi1]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h0, h1, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p149_1, u3ehi1]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h0, h147, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p149_1, u3ehi2]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h1, hlam, p149_1]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h3, hlam, p149_1]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [hlam, p149_0]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h6, hlam, p149_1]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h116, hlam, p149_1]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p149_1]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h4, hlam, p149_0]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h0, h1, h118, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p149_1, u3ehi1]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [hlam, p149_0]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h118, hlam, p149_0]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h2, hlam, p149_0]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h5, hlam, p149_1]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h1, h116, hc35, hlam, hphi, p149_1, u3ehi1]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h118, hc04, hc45, hlam, hphi, p149_1]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [hlam, p149_0]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h175 | h175
        · rcases m.htr 0 3 5 (by decide) (by decide) with h176 | h176
          · linarith only [h176, h3, h5, hlam]
          · linarith only [h175, h176, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h179 | h179
          · linarith only [h175, h179, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h181 | h181
            · linarith only [h181, h4, h5, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h183 | h183
              · linarith only [h179, h183, h3, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
              · linarith only [h183, h3, h5, hc35, hlam, hphi, u3ehi2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h186 | h186
      · rcases m.htr 0 3 4 (by decide) (by decide) with h187 | h187
        · linarith only [h187, h3, h4, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h189 | h189
          · linarith only [h187, h189, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h191 | h191
            · rcases m.htr 2 3 5 (by decide) (by decide) with h192 | h192
              · linarith only [h189, h192, h3, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
              · rcases h0bigk with h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [hlam, p194_0]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h186, hc01, hc25, hlam, hphi, ht0b, ht5b, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p194_1, u3ehi1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h191, hc01, hc45, hlam, hphi, ht0b, ht5b, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h186, h192, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p194_1, u3ehi2]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h0, hlam, p194_0]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [hlam, p194_0]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h1, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p194_1, u3ehi1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h4, hlam, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h4, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h1, hlam, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h3, hlam, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [hlam, p194_0]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h187, hlam, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h189, hlam, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h187, hc01, hc34, hlam, hphi, ht12, ht23, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h187, hc02, hc34, hlam, hphi, ht23, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h1, h187, hc34, hlam, hphi, p194_1, u3ehi1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [hlam, p194_0]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h186, h187, h192, hc34, hlam, hphi, p194_1, u3ehi2]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h2, hlam, p194_0]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h186, hlam, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h1, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p194_1, u3ehi1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h191, hlam, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [hlam, p194_0]
            · linarith only [h191, h3, h4, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h221 | h221
        · linarith only [h221, h3, h4, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h223 | h223
          · linarith only [h221, h223, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h225 | h225
            · rcases m.htr 2 3 5 (by decide) (by decide) with h226 | h226
              · linarith only [h223, h226, h3, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
              · linarith only [h186, h226, h3, hc35, hlam, hphi, u3ehi2]
            · linarith only [h225, h3, h4, hc45, hlam, hphi, ht34, u3ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h230 | h230
    · rcases m.htr 0 2 5 (by decide) (by decide) with h231 | h231
      · rcases m.htr 0 3 4 (by decide) (by decide) with h232 | h232
        · rcases m.htr 0 3 5 (by decide) (by decide) with h233 | h233
          · rcases m.htr 0 4 5 (by decide) (by decide) with h234 | h234
            · rcases m.htr 2 3 5 (by decide) (by decide) with h235 | h235
              · rcases h0bigk with h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [hlam, p236_0]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h231, h235, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p236_1, u3ehi4]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h231, h235, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p236_1, u3ehi4]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h234, hc01, hc45, hlam, hphi, ht0b, ht5b, p236_1]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h231, h235, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p236_1, u3ehi4]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h0, hlam, p236_0]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [hlam, p236_0]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h3, hlam, p236_0]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h234, hc02, hc45, hlam, hphi, ht0b, ht5b, p236_1]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h3, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p236_1]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h1, hlam, p236_1]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h3, hc02, hc23, hlam, hphi, p236_1]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [hlam, p236_0]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h234, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p236_1]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h231, h235, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p236_1, u3ehi4]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p236_1]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h230, hlam, p236_0]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h232, hlam, p236_0]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [hlam, p236_0]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h230, h231, h235, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p236_1, u3ehi4]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h2, hlam, p236_0]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h231, hlam, p236_1]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h233, hlam, p236_0]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [h234, hlam, p236_1]
                · have p236_0 := h236c.1
                  have p236_1 := h236c.2.1
                  have p236_2 := h236c.2.2.1
                  have p236_3 := h236c.2.2.2
                  linarith only [hlam, p236_0]
              · linarith only [h232, h235, h3, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h263 | h263
              · rcases h0bigk with h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [hlam, p264_0]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h231, h263, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p264_1, u3ehi4]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p264_1, u3ehi0]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h232, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p264_1, u3ehi3]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h231, h263, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p264_1, u3ehi4]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h0, hlam, p264_0]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [hlam, p264_0]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h3, hlam, p264_0]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h232, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p264_1, u3ehi3]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h3, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p264_1]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h1, hlam, p264_1]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h3, hc02, hc23, hlam, hphi, p264_1]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [hlam, p264_0]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h232, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p264_1, u3ehi3]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h231, h263, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p264_1, u3ehi4]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p264_1]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h230, hlam, p264_0]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h232, hlam, p264_0]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [hlam, p264_0]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h234, hlam, p264_0]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h2, hlam, p264_0]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h231, hlam, p264_1]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h233, hlam, p264_0]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [h230, h231, h3, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p264_1]
                · have p264_0 := h264c.1
                  have p264_1 := h264c.2.1
                  have p264_2 := h264c.2.2.1
                  have p264_3 := h264c.2.2.2
                  linarith only [hlam, p264_0]
              · linarith only [h230, h232, h263, h3, hc35, hlam, hphi, u3ehi3]
          · linarith only [h232, h233, hc35, hlam, hphi, u3ehi3]
        · linarith only [h230, h232, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h293 | h293
        · rcases m.htr 0 3 5 (by decide) (by decide) with h294 | h294
          · rcases m.htr 0 4 5 (by decide) (by decide) with h295 | h295
            · linarith only [h230, h231, h295, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h297 | h297
              · rcases h0bigk with h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [hlam, p298_0]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h230, h293, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p298_1, u3ehi3]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p298_1, u3ehi0]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h293, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p298_1, u3ehi3]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h230, h231, h293, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p298_1, u3ehi3]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h0, hlam, p298_0]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [hlam, p298_0]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h3, hlam, p298_0]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h293, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p298_1, u3ehi3]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h231, hlam, p298_0]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h1, hlam, p298_1]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h0, h3, hc12, hc23, hlam, hphi, p298_1]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [hlam, p298_0]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h293, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p298_1, u3ehi3]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h230, h231, h293, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p298_1, u3ehi3]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h295, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p298_1]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h230, hlam, p298_0]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h293, hlam, p298_0]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [hlam, p298_0]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h295, hlam, p298_0]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h2, hlam, p298_0]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h2, h230, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p298_1]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h294, hlam, p298_0]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [h293, h295, hc45, hlam, hphi, ht34, p298_1, u3ehi3]
                · have p298_0 := h298c.1
                  have p298_1 := h298c.2.1
                  have p298_2 := h298c.2.2.1
                  have p298_3 := h298c.2.2.2
                  linarith only [hlam, p298_0]
              · linarith only [h230, h293, h297, h3, hc35, hlam, hphi, u3ehi3]
          · linarith only [h293, h294, hc35, hlam, hphi, u3ehi3]
        · linarith only [h230, h293, h3, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h327 | h327
      · rcases m.htr 0 3 4 (by decide) (by decide) with h328 | h328
        · rcases m.htr 0 3 5 (by decide) (by decide) with h329 | h329
          · rcases m.htr 0 4 5 (by decide) (by decide) with h330 | h330
            · rcases m.htr 2 3 5 (by decide) (by decide) with h331 | h331
              · rcases h0bigk with h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [hlam, p332_0]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h327, h331, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p332_1, u3ehi4]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h230, h327, h328, h331, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p332_1, u3ehi4]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h230, h327, h331, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p332_1, u3ehi4]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h327, h331, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p332_1, u3ehi4]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h0, hlam, p332_0]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [hlam, p332_0]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h3, hlam, p332_0]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h230, hlam, p332_1]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h230, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p332_1]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h1, hlam, p332_1]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h327, h331, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p332_1, u3ehi4]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [hlam, p332_0]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h230, h3, h327, h331, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p332_1, u3ehi4]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h3, h327, h331, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p332_1, u3ehi4]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p332_1]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h230, h327, h331, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p332_1, u3ehi4]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h328, hlam, p332_0]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [hlam, p332_0]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h3, h327, h328, h331, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p332_1, u3ehi4]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h2, hlam, p332_0]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h327, hlam, p332_1]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h329, hlam, p332_0]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [h330, hlam, p332_1]
                · have p332_0 := h332c.1
                  have p332_1 := h332c.2.1
                  have p332_2 := h332c.2.2.1
                  have p332_3 := h332c.2.2.2
                  linarith only [hlam, p332_0]
              · linarith only [h3, h328, h331, hc35, hlam, hphi, u3ehi3]
            · linarith only [h230, h327, h330, hlam]
          · linarith only [h328, h329, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h361 | h361
          · linarith only [h328, h361, hc34, hlam, hphi, u3ehi4]
          · linarith only [h3, h327, h361, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h364 | h364
        · rcases m.htr 0 3 5 (by decide) (by decide) with h365 | h365
          · rcases m.htr 0 4 5 (by decide) (by decide) with h366 | h366
            · rcases m.htr 2 3 5 (by decide) (by decide) with h367 | h367
              · rcases h0bigk with h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [hlam, p368_0]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  rcases p368_3 (m.d 0 1) (by simp) with h370 | h370
                  · rcases p368_3 (m.d 0 2) (by simp) with h371 | h371
                    · linarith only [h0, h371, hlam]
                    · rcases p368_3 (m.d 0 3) (by simp) with h373 | h373
                      · linarith only [h1, h373, hlam]
                      · linarith only [h3, h373, hlam]
                  · linarith only [h0, h370, hlam]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h364, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p368_1, u3ehi3]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h365, h366, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p368_1, u3ehi4]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h365, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p368_1, u3ehi4]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h0, hlam, p368_0]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [hlam, p368_0]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h3, hlam, p368_0]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h230, hlam, p368_1]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h327, hlam, p368_0]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h1, hlam, p368_1]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h3, hc02, hc23, hlam, hphi, p368_1]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [hlam, p368_0]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h3, h365, h366, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p368_1, u3ehi4]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h3, h365, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p368_1, u3ehi4]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h0, h230, hc12, hc24, hlam, hphi, p368_1]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h364, hlam, p368_0]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [hlam, p368_0]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h3, h364, h365, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p368_1, u3ehi4]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h2, hlam, p368_0]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h0, h327, hc12, hc25, hlam, hphi, p368_1]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h365, hlam, p368_0]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [h366, hlam, p368_1]
                · have p368_0 := h368c.1
                  have p368_1 := h368c.2.1
                  have p368_2 := h368c.2.2.1
                  have p368_3 := h368c.2.2.2
                  linarith only [hlam, p368_0]
              · linarith only [h3, h364, h367, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h401 | h401
              · rcases h0bigk with h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [hlam, p402_0]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  rcases p402_3 (m.d 0 1) (by simp) with h404 | h404
                  · rcases p402_3 (m.d 0 2) (by simp) with h405 | h405
                    · linarith only [h0, h405, hlam]
                    · rcases p402_3 (m.d 0 3) (by simp) with h407 | h407
                      · linarith only [h1, h407, hlam]
                      · linarith only [h3, h407, hlam]
                  · linarith only [h0, h404, hlam]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h364, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p402_1, u3ehi3]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h364, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p402_1, u3ehi3]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h364, h366, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p402_1, u3ehi3]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h0, hlam, p402_0]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [hlam, p402_0]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h3, hlam, p402_0]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h230, hlam, p402_1]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h327, hlam, p402_0]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h1, hlam, p402_1]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h0, h3, hc12, hc23, hlam, hphi, p402_1]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [hlam, p402_0]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h0, h230, h3, hc12, hc23, hlam, hphi, p402_1]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h0, h3, h327, hc12, hc23, hlam, hphi, p402_1]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h366, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p402_1]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h0, h366, hc12, hc45, hlam, hphi, ht23, ht34, p402_1]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h364, hlam, p402_0]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [hlam, p402_0]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h366, hlam, p402_0]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h2, hlam, p402_0]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h0, h327, h401, hc12, hc23, hlam, hphi, p402_1]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h365, hlam, p402_0]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [h366, hc04, hc45, hlam, hphi, p402_1]
                · have p402_0 := h402c.1
                  have p402_1 := h402c.2.1
                  have p402_2 := h402c.2.2.1
                  have p402_3 := h402c.2.2.2
                  linarith only [hlam, p402_0]
              · linarith only [h3, h364, h401, hc35, hlam, hphi, u3ehi3]
          · linarith only [h364, h365, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h436 | h436
          · linarith only [h364, h436, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h438 | h438
            · rcases m.htr 2 3 5 (by decide) (by decide) with h439 | h439
              · rcases h0bigk with h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [hlam, p440_0]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  rcases p440_3 (m.d 0 1) (by simp) with h442 | h442
                  · rcases p440_3 (m.d 0 2) (by simp) with h443 | h443
                    · linarith only [h0, h443, hlam]
                    · rcases p440_3 (m.d 0 3) (by simp) with h445 | h445
                      · linarith only [h1, h445, hlam]
                      · linarith only [h3, h445, hlam]
                  · linarith only [h0, h442, hlam]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p440_1, u3ehi1]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h438, hc01, hc45, hlam, hphi, ht0b, ht5b, p440_1]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h1, h436, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p440_1, u3ehi1]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h0, hlam, p440_0]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [hlam, p440_0]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h3, hlam, p440_0]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h230, hlam, p440_1]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h327, hlam, p440_0]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h1, hlam, p440_1]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h0, h436, h439, hc12, hc23, hlam, hphi, p440_1]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [hlam, p440_0]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h364, hlam, p440_1]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h436, hlam, p440_1]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h0, h1, h436, h439, hc04, hc12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p440_1, u3ehi1]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h0, h230, hc12, hc24, hlam, hphi, p440_1]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h1, h364, hc34, hlam, hphi, p440_1, u3ehi1]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [hlam, p440_0]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h1, h364, h436, hc34, hlam, hphi, p440_1, u3ehi1]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h2, hlam, p440_0]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h0, h327, hc12, hc25, hlam, hphi, p440_1]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h1, h436, h439, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p440_1, u3ehi1]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [h438, hlam, p440_1]
                · have p440_0 := h440c.1
                  have p440_1 := h440c.2.1
                  have p440_2 := h440c.2.2.1
                  have p440_3 := h440c.2.2.2
                  linarith only [hlam, p440_0]
              · rcases h0bigk with h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [hlam, p472_0]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  rcases p472_3 (m.d 0 1) (by simp) with h474 | h474
                  · rcases p472_3 (m.d 0 2) (by simp) with h475 | h475
                    · linarith only [h0, h475, hlam]
                    · rcases p472_3 (m.d 0 3) (by simp) with h477 | h477
                      · linarith only [h1, h477, hlam]
                      · linarith only [h3, h477, hlam]
                  · linarith only [h0, h474, hlam]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p472_1, u3ehi1]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h1, h364, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p472_1, u3ehi1]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h1, h436, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p472_1, u3ehi1]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h0, hlam, p472_0]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [hlam, p472_0]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h3, hlam, p472_0]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h230, hlam, p472_1]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h327, hlam, p472_0]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h1, hlam, p472_1]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h0, h3, h439, hc12, hc35, hlam, hphi, ht23, p472_1]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [hlam, p472_0]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h364, hlam, p472_1]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h436, hlam, p472_1]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p472_1]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h0, h230, hc12, hc24, hlam, hphi, p472_1]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h364, hc34, hlam, hphi, p472_1, u3ehi0]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [hlam, p472_0]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h1, h364, h436, hc34, hlam, hphi, p472_1, u3ehi1]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h2, hlam, p472_0]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h0, h327, h439, hc12, hc35, hlam, hphi, ht23, p472_1]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h1, h327, h439, hc35, hlam, hphi, p472_1, u3ehi1]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [h438, hlam, p472_1]
                · have p472_0 := h472c.1
                  have p472_1 := h472c.2.1
                  have p472_2 := h472c.2.2.1
                  have p472_3 := h472c.2.2.2
                  linarith only [hlam, p472_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h504 | h504
              · rcases h0bigk with h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  rcases p505_3 (m.d 0 1) (by simp) with h507 | h507
                  · rcases p505_3 (m.d 0 2) (by simp) with h508 | h508
                    · linarith only [h0, h508, hlam]
                    · rcases p505_3 (m.d 0 3) (by simp) with h510 | h510
                      · linarith only [h1, h510, hlam]
                      · linarith only [h3, h510, hlam]
                  · linarith only [h0, h507, hlam]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p505_1, u3ehi1]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h1, h364, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p505_1, u3ehi1]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h1, h436, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p505_1, u3ehi1]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h0, hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h3, hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h230, hlam, p505_1]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h327, hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h1, hlam, p505_1]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h0, h436, h504, hc12, hc23, hlam, hphi, p505_1]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h364, hlam, p505_1]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h436, hlam, p505_1]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h0, h1, h436, h504, hc04, hc12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p505_1, u3ehi1]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h0, h230, hc12, hc24, hlam, hphi, p505_1]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h1, h364, hc34, hlam, hphi, p505_1, u3ehi1]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h438, hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h2, hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h0, h327, hc12, hc25, hlam, hphi, p505_1]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h1, h436, h504, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p505_1, u3ehi1]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h436, h504, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p505_1]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [hlam, p505_0]
              · rcases h0bigk with h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  rcases p537_3 (m.d 0 1) (by simp) with h539 | h539
                  · rcases p537_3 (m.d 0 2) (by simp) with h540 | h540
                    · linarith only [h0, h540, hlam]
                    · rcases p537_3 (m.d 0 3) (by simp) with h542 | h542
                      · linarith only [h1, h542, hlam]
                      · linarith only [h3, h542, hlam]
                  · linarith only [h0, h539, hlam]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p537_1, u3ehi1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h1, h364, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p537_1, u3ehi1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h1, h436, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p537_1, u3ehi1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h0, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h3, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h230, hlam, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h327, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h1, hlam, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h0, h3, hc12, hc23, hlam, hphi, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h364, hlam, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h436, hlam, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h438, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h0, h438, hc12, hc45, hlam, hphi, ht23, ht34, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h438, hc45, hlam, hphi, ht34, p537_1, u3ehi0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h438, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h2, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h0, h327, h504, hc12, hc35, hlam, hphi, ht23, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h1, h327, h504, hc35, hlam, hphi, p537_1, u3ehi1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h0, h230, h327, h504, hc12, hc35, hlam, hphi, ht23, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hlam, p537_0]

end R2N4
