import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5328000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
  · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
    · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
      · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
        · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
          · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
            · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
              · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h10, h16, h19, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h10, h16, h18, h19, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h10, h13, h18, h22, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h2bigk with h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h0, h17, hc01, hc35, hlam, hphi, ht0b, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      rcases p24_3 (m.d 0 2) (by simp) with h28 | h28
                      · rcases p24_3 (m.d 1 2) (by simp) with h29 | h29
                        · linarith only [h0, h29, hlam]
                        · linarith only [h11, h29, hlam]
                      · linarith only [h28, hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      rcases p24_3 (m.d 0 2) (by simp) with h33 | h33
                      · rcases p24_3 (m.d 1 2) (by simp) with h34 | h34
                        · linarith only [h0, h34, hlam]
                        · linarith only [h12, h34, hlam]
                      · linarith only [h33, hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h0, hlam, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h17, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h0, h16, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h4, hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h10, hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h0, h16, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h0, h10, hc01, hc25, hlam, hphi, ht0b, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h5, hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h11, hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h16, hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h18, hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h6, hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h12, hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h17, hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h0, h16, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [hlam, p24_0]
              · linarith only [h0, h10, h14, h16, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h59 | h59
              · linarith only [h0, h10, h13, h16, h59, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
                · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
                  · rcases h2bigk with h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, h10, h13, h16, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      rcases p63_3 (m.d 0 2) (by simp) with h66 | h66
                      · rcases p63_3 (m.d 1 2) (by simp) with h67 | h67
                        · linarith only [h0, h67, hlam]
                        · linarith only [h10, h67, hlam]
                      · linarith only [h66, hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, h61, hc01, hc45, hlam, hphi, ht0b, ht5b, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      rcases p63_3 (m.d 0 2) (by simp) with h72 | h72
                      · rcases p63_3 (m.d 1 2) (by simp) with h73 | h73
                        · linarith only [h0, h73, hlam]
                        · linarith only [h12, h73, hlam]
                      · linarith only [h72, hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, hlam, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, h61, hc01, hc45, hlam, hphi, ht0b, ht5b, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h4, hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h10, hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h16, hlam, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h59, hlam, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h5, hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h11, hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h13, h16, h59, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h6, hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h12, hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h61, hlam, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hlam, p63_0]
                  · linarith only [h15, h16, h2, h62, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                  · linarith only [h0, h10, h13, h16, h61, h98, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h10, h13, h15, h16, h98, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h101 | h101
            · rcases m.htr 2 3 5 (by decide) (by decide) with h102 | h102
              · rcases m.htr 2 4 5 (by decide) (by decide) with h103 | h103
                · linarith only [h0, h103, h11, h15, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h105 | h105
                  · linarith only [h101, h105, h11, h15, hlam]
                  · rcases h2bigk with h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [hlam, p107_0]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p107_1]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h0, h102, h105, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p107_1]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      rcases p107_3 (m.d 0 2) (by simp) with h111 | h111
                      · rcases p107_3 (m.d 1 2) (by simp) with h112 | h112
                        · linarith only [h0, h112, hlam]
                        · linarith only [h11, h112, hlam]
                      · linarith only [h111, hlam, p107_0]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      rcases p107_3 (m.d 0 2) (by simp) with h116 | h116
                      · rcases p107_3 (m.d 1 2) (by simp) with h117 | h117
                        · linarith only [h0, h117, hlam]
                        · linarith only [h117, h12, hlam]
                      · linarith only [h116, hlam, p107_0]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h0, hlam, p107_1]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [hlam, p107_0]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h102, h105, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p107_1]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h0, h101, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p107_1]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h0, h101, h103, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p107_1]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h4, hlam, p107_0]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h10, hlam, p107_0]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [hlam, p107_0]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h0, h101, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p107_1]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h0, h10, h101, h103, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p107_1]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h5, hlam, p107_0]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h11, hlam, p107_0]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h101, hlam, p107_0]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [hlam, p107_0]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h103, hlam, p107_0]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h6, hlam, p107_0]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h12, hlam, p107_0]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h102, hlam, p107_0]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [h0, h101, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p107_1]
                    · have p107_0 := h107c.1
                      have p107_1 := h107c.2.1
                      have p107_2 := h107c.2.2.1
                      have p107_3 := h107c.2.2.2
                      linarith only [hlam, p107_0]
              · linarith only [h0, h10, h101, h102, h14, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
              · linarith only [h0, h101, h13, h142, h15, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h144 | h144
                · linarith only [h101, h13, h144, h15, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h146 | h146
                  · linarith only [h13, h146, h15, hlam]
                  · rcases h2bigk with h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [hlam, p148_0]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p148_1]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      rcases p148_3 (m.d 0 2) (by simp) with h151 | h151
                      · rcases p148_3 (m.d 1 2) (by simp) with h152 | h152
                        · linarith only [h0, h152, hlam]
                        · linarith only [h10, h152, hlam]
                      · linarith only [h151, hlam, p148_0]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      rcases p148_3 (m.d 0 2) (by simp) with h156 | h156
                      · rcases p148_3 (m.d 1 2) (by simp) with h157 | h157
                        · linarith only [h0, h157, hlam]
                        · linarith only [h11, h157, hlam]
                      · linarith only [h156, hlam, p148_0]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      rcases p148_3 (m.d 0 2) (by simp) with h161 | h161
                      · rcases p148_3 (m.d 1 2) (by simp) with h162 | h162
                        · linarith only [h0, h162, hlam]
                        · linarith only [h12, h162, hlam]
                      · linarith only [h161, hlam, p148_0]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [h0, hlam, p148_1]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [hlam, p148_0]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p148_1]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p148_1]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p148_1]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [h4, hlam, p148_0]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [h10, hlam, p148_0]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [hlam, p148_0]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [h101, hlam, p148_1]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [h142, hlam, p148_1]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [h5, hlam, p148_0]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [h11, hlam, p148_0]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p148_1]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [hlam, p148_0]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [h144, hlam, p148_0]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [h6, hlam, p148_0]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [h12, hlam, p148_0]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p148_1]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [h14, h142, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p148_1]
                    · have p148_0 := h148c.1
                      have p148_1 := h148c.2.1
                      have p148_2 := h148c.2.2.1
                      have p148_3 := h148c.2.2.2
                      linarith only [hlam, p148_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h186 | h186
          · linarith only [h13, h14, h186, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h188 | h188
            · rcases m.htr 2 3 5 (by decide) (by decide) with h189 | h189
              · linarith only [h10, h14, h189, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h191 | h191
                · linarith only [h0, h11, h186, h191, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h193 | h193
                  · linarith only [h10, h14, h186, h188, h193, hlam]
                  · rcases h2bigk with h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [hlam, p195_0]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h0, h10, h188, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p195_1]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h0, h188, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p195_1]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      rcases p195_3 (m.d 0 2) (by simp) with h199 | h199
                      · rcases p195_3 (m.d 1 2) (by simp) with h200 | h200
                        · linarith only [h0, h200, hlam]
                        · linarith only [h11, h200, hlam]
                      · linarith only [h199, hlam, p195_0]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h0, h188, h189, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p195_1]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h0, hlam, p195_1]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [hlam, p195_0]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h188, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p195_1]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h0, h188, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p195_1]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p195_1]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h4, hlam, p195_0]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h10, hlam, p195_0]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [hlam, p195_0]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h10, h14, h188, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p195_1]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h189, hlam, p195_1]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h5, hlam, p195_0]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h11, hlam, p195_0]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h188, hlam, p195_0]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [hlam, p195_0]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h191, hlam, p195_0]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h6, hlam, p195_0]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h12, hlam, p195_0]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p195_1]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [h0, h12, h188, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p195_1]
                    · have p195_0 := h195c.1
                      have p195_1 := h195c.2.1
                      have p195_2 := h195c.2.2.1
                      have p195_3 := h195c.2.2.2
                      linarith only [hlam, p195_0]
            · linarith only [h0, h13, h14, h188, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h226 | h226
        · rcases m.htr 1 4 5 (by decide) (by decide) with h227 | h227
          · rcases m.htr 2 3 4 (by decide) (by decide) with h228 | h228
            · linarith only [h0, h13, h226, h228, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h230 | h230
              · rcases m.htr 2 4 5 (by decide) (by decide) with h231 | h231
                · rcases m.htr 3 4 5 (by decide) (by decide) with h232 | h232
                  · rcases h2bigk with h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [hlam, p233_0]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h0, h11, h228, h230, h232, hc01, hc45, hlam, hphi, ht0b, ht5b, p233_1]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h0, h230, h232, hc01, hc45, hlam, hphi, ht0b, ht5b, p233_1]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h0, h228, h230, h232, hc01, hc45, hlam, hphi, ht0b, ht5b, p233_1]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      rcases p233_3 (m.d 0 2) (by simp) with h238 | h238
                      · rcases p233_3 (m.d 1 2) (by simp) with h239 | h239
                        · linarith only [h0, h239, hlam]
                        · linarith only [h12, h239, hlam]
                      · linarith only [h238, hlam, p233_0]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h0, hlam, p233_1]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [hlam, p233_0]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h230, h232, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p233_1]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h0, h228, h230, h232, hc01, hc45, hlam, hphi, ht0b, ht5b, p233_1]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p233_1]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h4, hlam, p233_0]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h10, hlam, p233_0]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [hlam, p233_0]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h228, hlam, p233_1]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h10, h13, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p233_1]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h5, hlam, p233_0]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h11, hlam, p233_0]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p233_1]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [hlam, p233_0]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h0, h11, h230, h232, hc01, hc45, hlam, hphi, ht0b, ht5b, p233_1]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h6, hlam, p233_0]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h12, hlam, p233_0]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h230, hlam, p233_0]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [h231, hlam, p233_1]
                    · have p233_0 := h233c.1
                      have p233_1 := h233c.2.1
                      have p233_2 := h233c.2.2.1
                      have p233_3 := h233c.2.2.2
                      linarith only [hlam, p233_0]
                  · linarith only [h0, h10, h13, h230, h232, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h13, h226, h227, h228, h230, h231, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h13, h226, h230, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h13, h226, h227, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h267 | h267
          · rcases m.htr 2 3 4 (by decide) (by decide) with h268 | h268
            · linarith only [h10, h13, h268, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h270 | h270
              · linarith only [h10, h226, h270, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h272 | h272
                · rcases m.htr 3 4 5 (by decide) (by decide) with h273 | h273
                  · rcases h2bigk with h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [hlam, p274_0]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p274_1]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      rcases p274_3 (m.d 0 2) (by simp) with h277 | h277
                      · rcases p274_3 (m.d 1 2) (by simp) with h278 | h278
                        · linarith only [h0, h278, hlam]
                        · linarith only [h10, h278, hlam]
                      · linarith only [h277, hlam, p274_0]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h0, h272, hc01, hc45, hlam, hphi, ht0b, ht5b, p274_1]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      rcases p274_3 (m.d 0 2) (by simp) with h283 | h283
                      · rcases p274_3 (m.d 1 2) (by simp) with h284 | h284
                        · linarith only [h0, h284, hlam]
                        · linarith only [h12, h284, hlam]
                      · linarith only [h283, hlam, p274_0]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h0, hlam, p274_1]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [hlam, p274_0]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p274_1]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h0, h272, hc01, hc45, hlam, hphi, ht0b, ht5b, p274_1]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h0, h270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p274_1]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h4, hlam, p274_0]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h10, hlam, p274_0]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [hlam, p274_0]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h268, hlam, p274_1]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h270, hlam, p274_1]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h5, hlam, p274_0]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h11, hlam, p274_0]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h11, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p274_1]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [hlam, p274_0]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h0, h11, h270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p274_1]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h6, hlam, p274_0]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h12, hlam, p274_0]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p274_1]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [h272, hlam, p274_1]
                    · have p274_0 := h274c.1
                      have p274_1 := h274c.2.1
                      have p274_2 := h274c.2.2.1
                      have p274_3 := h274c.2.2.2
                      linarith only [hlam, p274_0]
                  · linarith only [h13, h267, h273, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h309 | h309
                  · rcases h2bigk with h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [hlam, p310_0]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p310_1]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      rcases p310_3 (m.d 0 2) (by simp) with h313 | h313
                      · rcases p310_3 (m.d 1 2) (by simp) with h314 | h314
                        · linarith only [h0, h314, hlam]
                        · linarith only [h10, h314, hlam]
                      · linarith only [h313, hlam, p310_0]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      rcases p310_3 (m.d 0 2) (by simp) with h318 | h318
                      · rcases p310_3 (m.d 1 2) (by simp) with h319 | h319
                        · linarith only [h0, h319, hlam]
                        · linarith only [h11, h319, hlam]
                      · linarith only [h318, hlam, p310_0]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      rcases p310_3 (m.d 0 2) (by simp) with h323 | h323
                      · rcases p310_3 (m.d 1 2) (by simp) with h324 | h324
                        · linarith only [h0, h324, hlam]
                        · linarith only [h12, h324, hlam]
                      · linarith only [h323, hlam, p310_0]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [h0, hlam, p310_1]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [hlam, p310_0]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p310_1]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p310_1]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p310_1]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [h4, hlam, p310_0]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [h10, hlam, p310_0]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [hlam, p310_0]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [h268, hlam, p310_1]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [h270, hlam, p310_1]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [h5, hlam, p310_0]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [h11, hlam, p310_0]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p310_1]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [hlam, p310_0]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [h272, hlam, p310_0]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [h6, hlam, p310_0]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [h12, hlam, p310_0]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p310_1]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [h0, h13, h267, h272, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p310_1]
                    · have p310_0 := h310c.1
                      have p310_1 := h310c.2.1
                      have p310_2 := h310c.2.2.1
                      have p310_3 := h310c.2.2.2
                      linarith only [hlam, p310_0]
                  · linarith only [h13, h267, h309, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h349 | h349
            · linarith only [h10, h13, h349, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h351 | h351
              · linarith only [h10, h226, h351, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h353 | h353
                · linarith only [h0, h11, h267, h353, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h355 | h355
                  · rcases h2bigk with h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [hlam, p356_0]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p356_1]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      rcases p356_3 (m.d 0 2) (by simp) with h359 | h359
                      · rcases p356_3 (m.d 1 2) (by simp) with h360 | h360
                        · linarith only [h0, h360, hlam]
                        · linarith only [h10, h360, hlam]
                      · linarith only [h359, hlam, p356_0]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      rcases p356_3 (m.d 0 2) (by simp) with h364 | h364
                      · rcases p356_3 (m.d 1 2) (by simp) with h365 | h365
                        · linarith only [h0, h365, hlam]
                        · linarith only [h11, h365, hlam]
                      · linarith only [h364, hlam, p356_0]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      rcases p356_3 (m.d 0 2) (by simp) with h369 | h369
                      · rcases p356_3 (m.d 1 2) (by simp) with h370 | h370
                        · linarith only [h0, h370, hlam]
                        · linarith only [h12, h370, hlam]
                      · linarith only [h369, hlam, p356_0]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [h0, hlam, p356_1]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [hlam, p356_0]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p356_1]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [h0, h349, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p356_1]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p356_1]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [h4, hlam, p356_0]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [h10, hlam, p356_0]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [hlam, p356_0]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [h349, hlam, p356_1]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [h351, hlam, p356_1]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [h5, hlam, p356_0]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [h11, hlam, p356_0]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p356_1]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [hlam, p356_0]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [h353, hlam, p356_0]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [h6, hlam, p356_0]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [h12, hlam, p356_0]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p356_1]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [h12, h267, h355, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p356_1]
                    · have p356_0 := h356c.1
                      have p356_1 := h356c.2.1
                      have p356_2 := h356c.2.2.1
                      have p356_3 := h356c.2.2.2
                      linarith only [hlam, p356_0]
                  · rcases h2bigk with h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [hlam, p394_0]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [h0, h12, hc01, hc25, hlam, hphi, ht0b, ht5b, p394_1]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      rcases p394_3 (m.d 0 2) (by simp) with h397 | h397
                      · rcases p394_3 (m.d 1 2) (by simp) with h398 | h398
                        · linarith only [h0, h398, hlam]
                        · linarith only [h10, h398, hlam]
                      · linarith only [h397, hlam, p394_0]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      rcases p394_3 (m.d 0 2) (by simp) with h402 | h402
                      · rcases p394_3 (m.d 1 2) (by simp) with h403 | h403
                        · linarith only [h0, h403, hlam]
                        · linarith only [h11, h403, hlam]
                      · linarith only [h402, hlam, p394_0]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      rcases p394_3 (m.d 0 2) (by simp) with h407 | h407
                      · rcases p394_3 (m.d 1 2) (by simp) with h408 | h408
                        · linarith only [h0, h408, hlam]
                        · linarith only [h12, h408, hlam]
                      · linarith only [h407, hlam, p394_0]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [h0, hlam, p394_1]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [hlam, p394_0]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p394_1]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [h0, h349, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p394_1]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [h0, h349, h353, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p394_1]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [h4, hlam, p394_0]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [h10, hlam, p394_0]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [hlam, p394_0]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [h349, hlam, p394_1]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [h351, hlam, p394_1]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [h5, hlam, p394_0]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [h11, hlam, p394_0]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p394_1]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [hlam, p394_0]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [h353, hlam, p394_0]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [h6, hlam, p394_0]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [h12, hlam, p394_0]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p394_1]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [h0, h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p394_1]
                    · have p394_0 := h394c.1
                      have p394_1 := h394c.2.1
                      have p394_2 := h394c.2.2.1
                      have p394_3 := h394c.2.2.2
                      linarith only [hlam, p394_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h432 | h432
      · rcases m.htr 1 3 5 (by decide) (by decide) with h433 | h433
        · linarith only [h10, h12, h433, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h435 | h435
          · linarith only [h11, h12, h435, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h437 | h437
            · linarith only [h0, h10, h12, h437, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h12, h432, h437, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h440 | h440
        · linarith only [h11, h12, h432, h440, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h442 | h442
          · linarith only [h11, h12, h442, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h444 | h444
            · linarith only [h0, h10, h12, h432, h444, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h446 | h446
              · linarith only [h10, h12, h440, h446, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h448 | h448
                · linarith only [h0, h11, h12, h4, h446, h448, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h450 | h450
                  · linarith only [h11, h12, h444, h448, h450, hc23, hc34, hlam, hphi]
                  · rcases h2bigk with h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h0, h11, h444, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      rcases p452_3 (m.d 0 2) (by simp) with h455 | h455
                      · rcases p452_3 (m.d 1 2) (by simp) with h456 | h456
                        · linarith only [h0, h456, hlam]
                        · linarith only [h10, h456, hlam]
                      · linarith only [h455, hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      rcases p452_3 (m.d 0 2) (by simp) with h460 | h460
                      · rcases p452_3 (m.d 1 2) (by simp) with h461 | h461
                        · linarith only [h0, h461, hlam]
                        · linarith only [h11, h461, hlam]
                      · linarith only [h460, hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h0, h11, h12, h444, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h0, hlam, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h12, h446, h450, h7, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h12, h446, h450, h7, h9, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h12, hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h4, hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h10, hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h444, hlam, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h446, hlam, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h5, hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h11, hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h448, hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h6, hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h0, h4, h446, h450, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h0, h4, h446, h450, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h0, h4, h444, h446, h450, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [hlam, p452_0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h486 | h486
    · rcases m.htr 1 3 4 (by decide) (by decide) with h487 | h487
      · linarith only [h10, h11, h487, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h489 | h489
        · rcases m.htr 1 4 5 (by decide) (by decide) with h490 | h490
          · rcases m.htr 2 3 4 (by decide) (by decide) with h491 | h491
            · linarith only [h0, h10, h11, h487, h491, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h493 | h493
              · linarith only [h0, h10, h11, h4, h491, h493, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h10, h11, h4, h489, h491, h493, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h10, h11, h489, h490, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h497 | h497
          · rcases m.htr 2 3 4 (by decide) (by decide) with h498 | h498
            · linarith only [h0, h10, h487, h497, h498, hc01, hc45, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h500 | h500
              · linarith only [h10, h489, h500, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h502 | h502
                · rcases m.htr 3 4 5 (by decide) (by decide) with h503 | h503
                  · rcases h2bigk with h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [hlam, p504_0]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h0, h486, h500, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p504_1]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      rcases p504_3 (m.d 0 2) (by simp) with h507 | h507
                      · rcases p504_3 (m.d 1 2) (by simp) with h508 | h508
                        · linarith only [h0, h508, hlam]
                        · linarith only [h10, h508, hlam]
                      · linarith only [h507, hlam, p504_0]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h0, h11, h486, h500, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p504_1]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      rcases p504_3 (m.d 0 2) (by simp) with h513 | h513
                      · rcases p504_3 (m.d 1 2) (by simp) with h514 | h514
                        · linarith only [h0, h514, hlam]
                        · linarith only [h486, h514, hlam]
                      · linarith only [h513, hlam, p504_0]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h0, hlam, p504_1]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [hlam, p504_0]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h11, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p504_1]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h11, hlam, p504_0]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h0, h11, h5, h500, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p504_1]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h4, hlam, p504_0]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h10, hlam, p504_0]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [hlam, p504_0]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h498, hlam, p504_1]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h500, hlam, p504_1]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h5, hlam, p504_0]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h0, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p504_1]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h0, h4, h498, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p504_1]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [hlam, p504_0]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h0, h4, h498, h500, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p504_1]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h6, hlam, p504_0]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h486, hlam, p504_0]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h486, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p504_1]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [h502, hlam, p504_1]
                    · have p504_0 := h504c.1
                      have p504_1 := h504c.2.1
                      have p504_2 := h504c.2.2.1
                      have p504_3 := h504c.2.2.2
                      linarith only [hlam, p504_0]
                  · linarith only [h0, h10, h11, h4, h498, h503, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h11, h486, h497, h502, hlam]
          · linarith only [h11, h486, h497, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h541 | h541
      · linarith only [h10, h11, h541, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h543 | h543
        · linarith only [h10, h486, h543, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h545 | h545
          · rcases m.htr 2 3 4 (by decide) (by decide) with h546 | h546
            · linarith only [h0, h10, h486, h541, h546, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h548 | h548
              · linarith only [h0, h10, h11, h4, h543, h546, h548, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h550 | h550
                · rcases m.htr 3 4 5 (by decide) (by decide) with h551 | h551
                  · rcases h2bigk with h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [hlam, p552_0]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p552_1]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      rcases p552_3 (m.d 0 2) (by simp) with h555 | h555
                      · rcases p552_3 (m.d 1 2) (by simp) with h556 | h556
                        · linarith only [h0, h556, hlam]
                        · linarith only [h10, h556, hlam]
                      · linarith only [h555, hlam, p552_0]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h0, h10, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p552_1]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h0, h10, h486, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p552_1]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h0, hlam, p552_1]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [hlam, p552_0]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h11, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p552_1]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h11, hlam, p552_0]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h486, hlam, p552_0]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h4, hlam, p552_0]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h10, hlam, p552_0]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [hlam, p552_0]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h546, hlam, p552_1]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h548, hlam, p552_1]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h5, hlam, p552_0]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p552_1]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h0, h4, h546, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p552_1]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [hlam, p552_0]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h0, h10, h4, h486, h546, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p552_1]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h6, hlam, p552_0]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h10, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p552_1]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h0, h4, h548, h551, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p552_1]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [h550, hlam, p552_1]
                    · have p552_0 := h552c.1
                      have p552_1 := h552c.2.1
                      have p552_2 := h552c.2.2.1
                      have p552_3 := h552c.2.2.2
                      linarith only [hlam, p552_0]
                  · linarith only [h0, h10, h11, h4, h546, h551, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h10, h11, h545, h550, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h584 | h584
            · linarith only [h0, h10, h11, h5, h584, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h586 | h586
              · linarith only [h0, h10, h11, h4, h545, h586, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h588 | h588
                · linarith only [h10, h11, h545, h584, h588, hc23, hc34, hlam, hphi]
                · linarith only [h0, h10, h11, h4, h588, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

end R2N4
