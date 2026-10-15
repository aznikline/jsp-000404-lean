import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4354000 in
set_option maxHeartbeats 4354000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h4ehi := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
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
                  linarith only [h4, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi4]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p10_1, u4ehi0]
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
                  linarith only [h4, h9, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi4]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p10_1, u4ehi4]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h5, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi4]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h1, hlam, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h4, hlam, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h8, hc03, hlam, hphi, ht0b, ht45, ht5b, p10_1, u4ehi4]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h4, h5, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi4]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h2, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h4, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi0]
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
                  linarith only [h5, h6, h9, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi4]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h3, hlam, p10_0]
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
                  linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi0]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi0]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p36_1, u4ehi0]
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
                  linarith only [h0, h7, h8, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi2]
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
                  linarith only [h4, hlam, p36_1]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [hlam, p36_0]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h7, h8, h9, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi2]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi2]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h2, hlam, p36_0]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h4, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi0]
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
                  linarith only [h0, h4, h6, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u3ehi2]
                · have p36_0 := h36c.1
                  have p36_1 := h36c.2.1
                  have p36_2 := h36c.2.2.1
                  have p36_3 := h36c.2.2.2
                  linarith only [h3, hlam, p36_0]
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
                  linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p63_1, u4ehi0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h2, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p63_1, u4ehi1]
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
                  linarith only [h1, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi3]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, h5, h62, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi4]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h1, hlam, p63_1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h4, hlam, p63_1]
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
                  linarith only [h0, h4, h5, h62, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi4]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h2, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h4, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi0]
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
                  linarith only [h3, hlam, p63_0]
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
                  linarith only [hc05, hlam, hphi, ht0b, ht45, ht5b, p63_1, u4ehi0]
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
                  linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1, u3ehi2]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h62, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1, u3ehi2]
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
                  linarith only [h4, hlam, p89_1]
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
                  linarith only [h0, h4, h62, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1, u3ehi2]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h2, hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h4, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1, u3ehi0]
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
                  linarith only [h3, hlam, p89_0]
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
                  linarith only [hc05, hlam, hphi, ht0b, ht45, ht5b, p89_1, u4ehi0]
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
              · linarith only [h116, h119, h4, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
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
                  linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p121_1, u3ehi2]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p121_1, u3ehi1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h118, hc01, hlam, hphi, ht0b, ht45, ht5b, p121_1, u4ehi4]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h1, h116, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p121_1, u3ehi1]
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
                  linarith only [h0, h118, hc01, hlam, hphi, ht0b, ht45, ht5b, p121_1, u4ehi4]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h0, h1, h116, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p121_1, u3ehi1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h1, hlam, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h4, hlam, p121_1]
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
                  linarith only [h2, hlam, p121_0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h4, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p121_1, u3ehi2]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h1, h6, hc34, hlam, hphi, p121_1, u3ehi1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [hlam, p121_0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h1, h116, h6, hc34, hlam, hphi, p121_1, u3ehi1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h3, hlam, p121_0]
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
              · linarith only [h1, h116, h147, h4, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
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
                  linarith only [h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p149_1]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p149_1, u3ehi1]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p149_1, u4ehi0]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h1, h116, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p149_1, u3ehi1]
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
                  linarith only [h0, h1, h118, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p149_1, u3ehi1]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h1, hlam, p149_1]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h4, hlam, p149_1]
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
                  linarith only [h2, hlam, p149_0]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h4, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p149_1, u3ehi2]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [h1, h6, hc34, hlam, hphi, p149_1, u3ehi1]
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
                  linarith only [h3, hlam, p149_0]
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
                  linarith only [h118, hc45, hlam, hphi, p149_1, u4ehi0]
                · have p149_0 := h149c.1
                  have p149_1 := h149c.2.1
                  have p149_2 := h149c.2.2.1
                  have p149_3 := h149c.2.2.2
                  linarith only [hlam, p149_0]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h175 | h175
        · rcases m.htr 0 3 5 (by decide) (by decide) with h176 | h176
          · linarith only [h176, h4, h5, hlam]
          · linarith only [h175, h176, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h179 | h179
          · linarith only [h175, h179, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h181 | h181
            · rcases m.htr 2 3 5 (by decide) (by decide) with h182 | h182
              · linarith only [h1, h179, h181, h182, h2, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h182, h4, h5, hc35, hlam, hphi, u3ehi2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
              · linarith only [h185, h4, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
              · linarith only [h185, h4, h5, hc35, hlam, hphi, u3ehi2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h188 | h188
      · rcases m.htr 0 3 4 (by decide) (by decide) with h189 | h189
        · rcases m.htr 0 3 5 (by decide) (by decide) with h190 | h190
          · rcases m.htr 0 4 5 (by decide) (by decide) with h191 | h191
            · rcases m.htr 2 3 5 (by decide) (by decide) with h192 | h192
              · rcases h0bigk with h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [hlam, p193_0]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h188, h192, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p193_1, u3ehi4]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h188, h192, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p193_1, u3ehi4]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p193_1, u4ehi0]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h188, h192, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p193_1, u3ehi4]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h0, hlam, p193_0]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [hlam, p193_0]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h4, hlam, p193_0]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h191, hc02, hlam, hphi, ht0b, ht45, ht5b, p193_1, u4ehi4]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h188, h192, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p193_1, u3ehi4]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h1, hlam, p193_1]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h4, hc02, hc23, hlam, hphi, p193_1]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [hlam, p193_0]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h191, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p193_1, u4ehi4]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h188, h192, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p193_1, u3ehi4]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h2, hlam, p193_0]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h188, h192, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p193_1, u3ehi4]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h189, hlam, p193_0]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [hlam, p193_0]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h188, h189, h192, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p193_1, u3ehi4]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h3, hlam, p193_0]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h188, hlam, p193_1]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h190, hlam, p193_0]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [h191, hlam, p193_1]
                · have p193_0 := h193c.1
                  have p193_1 := h193c.2.1
                  have p193_2 := h193c.2.2.1
                  have p193_3 := h193c.2.2.2
                  linarith only [hlam, p193_0]
              · linarith only [h189, h192, h4, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h220 | h220
              · rcases h0bigk with h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [hlam, p221_0]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [h188, h220, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p221_1, u3ehi4]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p221_1, u3ehi0]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p221_1, u4ehi0]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [h188, h220, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p221_1, u3ehi4]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [h0, hlam, p221_0]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [hlam, p221_0]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [h4, hlam, p221_0]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [h189, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p221_1, u3ehi3]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [h188, h220, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p221_1, u3ehi4]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [h1, hlam, p221_1]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [h4, hc02, hc23, hlam, hphi, p221_1]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [hlam, p221_0]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [h189, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p221_1, u3ehi3]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [h188, h220, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p221_1, u3ehi4]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [h2, hlam, p221_0]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [h188, h220, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p221_1, u3ehi4]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [h189, hlam, p221_0]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [hlam, p221_0]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [h191, hlam, p221_0]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [h3, hlam, p221_0]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [h188, hlam, p221_1]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [h190, hlam, p221_0]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [hc05, hlam, hphi, ht0b, ht45, ht5b, p221_1, u4ehi0]
                · have p221_0 := h221c.1
                  have p221_1 := h221c.2.1
                  have p221_2 := h221c.2.2.1
                  have p221_3 := h221c.2.2.2
                  linarith only [hlam, p221_0]
              · linarith only [h189, h220, h4, hc35, hlam, hphi, u3ehi3]
          · linarith only [h189, h190, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h249 | h249
          · linarith only [h189, h249, hc34, hlam, hphi, u3ehi4]
          · linarith only [h188, h249, h4, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h252 | h252
        · rcases m.htr 0 3 5 (by decide) (by decide) with h253 | h253
          · rcases m.htr 0 4 5 (by decide) (by decide) with h254 | h254
            · rcases m.htr 2 3 5 (by decide) (by decide) with h255 | h255
              · rcases h0bigk with h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [hlam, p256_0]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  rcases p256_3 (m.d 0 1) (by simp) with h258 | h258
                  · rcases p256_3 (m.d 0 2) (by simp) with h259 | h259
                    · linarith only [h0, h259, hlam]
                    · rcases p256_3 (m.d 0 3) (by simp) with h261 | h261
                      · linarith only [h1, h261, hlam]
                      · linarith only [h261, h4, hlam]
                  · linarith only [h0, h258, hlam]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h252, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p256_1, u3ehi3]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p256_1, u4ehi0]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h253, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p256_1, u3ehi4]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h0, hlam, p256_0]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [hlam, p256_0]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h4, hlam, p256_0]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h254, hc02, hlam, hphi, ht0b, ht45, ht5b, p256_1, u4ehi4]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h188, hlam, p256_0]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h1, hlam, p256_1]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p256_1]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [hlam, p256_0]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h254, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p256_1, u4ehi4]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h0, h188, h4, hc12, hc23, hlam, hphi, p256_1]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h2, hlam, p256_0]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h0, h252, h4, hc12, hc23, hlam, hphi, p256_1]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h252, hlam, p256_0]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [hlam, p256_0]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h252, h253, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p256_1, u3ehi4]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h3, hlam, p256_0]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h0, h188, h255, hc12, hc23, hlam, hphi, p256_1]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h253, hlam, p256_0]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [h254, hlam, p256_1]
                · have p256_0 := h256c.1
                  have p256_1 := h256c.2.1
                  have p256_2 := h256c.2.2.1
                  have p256_3 := h256c.2.2.2
                  linarith only [hlam, p256_0]
              · linarith only [h252, h255, h4, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h289 | h289
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
                  rcases p290_3 (m.d 0 1) (by simp) with h292 | h292
                  · rcases p290_3 (m.d 0 2) (by simp) with h293 | h293
                    · linarith only [h0, h293, hlam]
                    · rcases p290_3 (m.d 0 3) (by simp) with h295 | h295
                      · linarith only [h1, h295, hlam]
                      · linarith only [h295, h4, hlam]
                  · linarith only [h0, h292, hlam]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [h252, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p290_1, u3ehi3]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p290_1, u4ehi0]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [h2, h254, hc01, hlam, hphi, ht0b, ht45, ht5b, p290_1, u4ehi1]
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
                  linarith only [h4, hlam, p290_0]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [h252, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p290_1, u3ehi3]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [h188, hlam, p290_0]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [h1, hlam, p290_1]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [h4, hc02, hc23, hlam, hphi, p290_1]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [hlam, p290_0]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [h252, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p290_1, u3ehi3]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [h252, h254, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p290_1, u3ehi3]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [h2, hlam, p290_0]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [h0, h254, hc12, hc45, hlam, hphi, ht23, ht34, p290_1]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [h252, hlam, p290_0]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [hlam, p290_0]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [h254, hlam, p290_0]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [h3, hlam, p290_0]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [h0, h188, h289, hc12, hc23, hlam, hphi, p290_1]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [h253, hlam, p290_0]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [h254, hc45, hlam, hphi, p290_1, u4ehi0]
                · have p290_0 := h290c.1
                  have p290_1 := h290c.2.1
                  have p290_2 := h290c.2.2.1
                  have p290_3 := h290c.2.2.2
                  linarith only [hlam, p290_0]
              · linarith only [h253, h289, h4, hlam]
          · linarith only [h252, h253, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h324 | h324
          · linarith only [h252, h324, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h326 | h326
            · rcases m.htr 2 3 5 (by decide) (by decide) with h327 | h327
              · rcases h0bigk with h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  rcases p328_3 (m.d 0 1) (by simp) with h330 | h330
                  · rcases p328_3 (m.d 0 2) (by simp) with h331 | h331
                    · linarith only [h0, h331, hlam]
                    · rcases p328_3 (m.d 0 3) (by simp) with h333 | h333
                      · linarith only [h1, h333, hlam]
                      · linarith only [h333, h4, hlam]
                  · linarith only [h0, h330, hlam]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p328_1, u3ehi0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h326, hc01, hlam, hphi, ht0b, ht45, ht5b, p328_1, u4ehi4]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h1, h324, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p328_1, u3ehi1]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h0, hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h4, hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h326, hc02, hlam, hphi, ht0b, ht45, ht5b, p328_1, u4ehi4]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h188, hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h1, hlam, p328_1]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p328_1]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h252, hlam, p328_1]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h324, hlam, p328_1]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h2, hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h0, h1, h252, h324, h327, hc12, hc23, hc34, hlam, hphi, p328_1, u3ehi1]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h1, h252, hc34, hlam, hphi, p328_1, u3ehi1]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h0, h1, h188, h252, h324, h327, hc12, hc23, hc34, hlam, hphi, p328_1, u3ehi1]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h3, hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h0, h188, h327, hc12, hc23, hlam, hphi, p328_1]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h1, h324, h327, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p328_1, u3ehi1]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h326, hlam, p328_1]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [hlam, p328_0]
              · rcases h0bigk with h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  rcases p360_3 (m.d 0 1) (by simp) with h362 | h362
                  · rcases p360_3 (m.d 0 2) (by simp) with h363 | h363
                    · linarith only [h0, h363, hlam]
                    · rcases p360_3 (m.d 0 3) (by simp) with h365 | h365
                      · linarith only [h1, h365, hlam]
                      · linarith only [h365, h4, hlam]
                  · linarith only [h0, h362, hlam]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p360_1, u3ehi1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p360_1, u4ehi0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h1, h324, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p360_1, u3ehi1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h0, hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h4, hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h326, h327, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p360_1, u4ehi4]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h188, hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h1, hlam, p360_1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h0, h327, h4, hc12, hc35, hlam, hphi, ht23, p360_1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h252, hlam, p360_1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h324, hlam, p360_1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h2, hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h0, h252, hc12, hc34, hlam, hphi, ht23, p360_1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h252, hc34, hlam, hphi, p360_1, u3ehi0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h0, h188, h252, hc12, hc34, hlam, hphi, ht23, p360_1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h3, hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h0, h188, h327, hc12, hc35, hlam, hphi, ht23, p360_1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h1, h188, h327, hc35, hlam, hphi, p360_1, u3ehi1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h326, hlam, p360_1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [hlam, p360_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h392 | h392
              · rcases h0bigk with h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [hlam, p393_0]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  rcases p393_3 (m.d 0 1) (by simp) with h395 | h395
                  · rcases p393_3 (m.d 0 2) (by simp) with h396 | h396
                    · linarith only [h0, h396, hlam]
                    · rcases p393_3 (m.d 0 3) (by simp) with h398 | h398
                      · linarith only [h1, h398, hlam]
                      · linarith only [h398, h4, hlam]
                  · linarith only [h0, h395, hlam]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p393_1, u3ehi1]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p393_1, u4ehi0]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h1, h324, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p393_1, u3ehi1]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h0, hlam, p393_0]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [hlam, p393_0]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h4, hlam, p393_0]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h1, h252, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p393_1, u3ehi1]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h188, hlam, p393_0]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h1, hlam, p393_1]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h324, h392, hc02, hc23, hlam, hphi, p393_1]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [hlam, p393_0]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h252, hlam, p393_1]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h324, hlam, p393_1]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h2, hlam, p393_0]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h0, h188, h326, hc12, hc25, hlam, hphi, p393_1]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h1, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p393_1, u3ehi1]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [hlam, p393_0]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h326, hlam, p393_0]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h3, hlam, p393_0]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h0, h188, hc12, hc25, hlam, hphi, p393_1]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h1, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p393_1, u3ehi1]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [h324, h392, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p393_1, u4ehi0]
                · have p393_0 := h393c.1
                  have p393_1 := h393c.2.1
                  have p393_2 := h393c.2.2.1
                  have p393_3 := h393c.2.2.2
                  linarith only [hlam, p393_0]
              · rcases h0bigk with h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  rcases p425_3 (m.d 0 1) (by simp) with h427 | h427
                  · rcases p425_3 (m.d 0 2) (by simp) with h428 | h428
                    · linarith only [h0, h428, hlam]
                    · rcases p425_3 (m.d 0 3) (by simp) with h430 | h430
                      · linarith only [h1, h430, hlam]
                      · linarith only [h4, h430, hlam]
                  · linarith only [h0, h427, hlam]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p425_1, u3ehi1]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h1, h252, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p425_1, u3ehi1]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h1, h324, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p425_1, u3ehi1]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h0, hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h4, hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h1, h252, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p425_1, u3ehi1]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h188, hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h1, hlam, p425_1]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h0, h392, h4, hc12, hc35, hlam, hphi, ht23, p425_1]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h252, hlam, p425_1]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h324, hlam, p425_1]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h2, hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h0, h326, hc12, hc45, hlam, hphi, ht23, ht34, p425_1]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h326, hc45, hlam, hphi, ht34, p425_1, u3ehi0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h326, hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h3, hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h0, h188, h392, hc12, hc35, hlam, hphi, ht23, p425_1]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h1, h188, h392, hc35, hlam, hphi, p425_1, u3ehi1]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h188, h392, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p425_1, u4ehi0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [hlam, p425_0]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h457 | h457
    · rcases m.htr 0 2 5 (by decide) (by decide) with h458 | h458
      · linarith only [h0, h3, h458, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h460 | h460
        · rcases m.htr 0 3 5 (by decide) (by decide) with h461 | h461
          · linarith only [h0, h3, h457, h461, hlam]
          · linarith only [h460, h461, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h464 | h464
          · linarith only [h460, h464, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h466 | h466
            · linarith only [h2, h3, h466, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h468 | h468
              · linarith only [h457, h458, h464, h468, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
              · linarith only [h457, h458, h468, hc35, hlam, hphi, u3ehi2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h471 | h471
      · linarith only [h0, h3, h471, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h473 | h473
        · rcases m.htr 0 3 5 (by decide) (by decide) with h474 | h474
          · linarith only [h1, h3, h474, hlam]
          · linarith only [h473, h474, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h477 | h477
          · linarith only [h473, h477, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h479 | h479
            · linarith only [h2, h3, h479, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h481 | h481
              · rcases h0bigk with h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [hlam, p482_0]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h3, h477, h481, hc02, hc23, hlam, hphi, p482_1]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h3, h477, h481, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p482_1, u3ehi0]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h3, h477, h481, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p482_1, u4ehi0]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h3, hlam, p482_1]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h0, hlam, p482_0]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [hlam, p482_0]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h457, hlam, p482_0]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h1, h473, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p482_1, u3ehi1]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h471, hlam, p482_0]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h1, hlam, p482_1]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h473, hc02, hc34, hlam, hphi, ht23, p482_1]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [hlam, p482_0]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h473, hlam, p482_1]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h477, hlam, p482_1]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h2, hlam, p482_0]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h0, h1, h3, h477, h479, h481, hc12, hc23, hc45, hlam, hphi, ht34, p482_1, u3ehi1]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h479, hc45, hlam, hphi, ht34, p482_1, u3ehi0]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [hlam, p482_0]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h479, hlam, p482_0]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h1, h477, h481, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p482_1, u3ehi1]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h0, h477, h481, hc12, hc23, hlam, hphi, p482_1]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h1, h477, h481, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p482_1, u3ehi1]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [h477, h481, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p482_1, u4ehi0]
                · have p482_0 := h482c.1
                  have p482_1 := h482c.2.1
                  have p482_2 := h482c.2.2.1
                  have p482_3 := h482c.2.2.2
                  linarith only [hlam, p482_0]
              · rcases h0bigk with h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [hlam, p508_0]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h0, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p508_1]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h1, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p508_1, u3ehi1]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h1, h3, h473, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p508_1, u3ehi1]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h3, hlam, p508_1]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h0, hlam, p508_0]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [hlam, p508_0]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h457, hlam, p508_0]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h1, h473, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p508_1, u3ehi1]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h471, hlam, p508_0]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h1, hlam, p508_1]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h0, h1, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p508_1]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [hlam, p508_0]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h473, hlam, p508_1]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h477, hlam, p508_1]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h2, hlam, p508_0]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h0, h479, hc12, hc45, hlam, hphi, ht23, ht34, p508_1]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h479, hc45, hlam, hphi, ht34, p508_1, u3ehi0]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [hlam, p508_0]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h479, hlam, p508_0]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h479, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p508_1]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h0, h479, hc12, hc45, hlam, hphi, ht23, ht34, p508_1]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h1, h479, hc45, hlam, hphi, ht34, p508_1, u3ehi1]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [h479, hc45, hlam, hphi, p508_1, u4ehi0]
                · have p508_0 := h508c.1
                  have p508_1 := h508c.2.1
                  have p508_2 := h508c.2.2.1
                  have p508_3 := h508c.2.2.2
                  linarith only [hlam, p508_0]

end R2N4
