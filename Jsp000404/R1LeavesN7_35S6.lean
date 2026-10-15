import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h5 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
  · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
    · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
      · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
        · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
          · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
            · linarith only [h0, h11, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
              · linarith only [h0, h10, h11, h13, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases h2bigk with h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [hlam, p15_0]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht5b, p15_1, u5ehi1]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h0, h10, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  rcases p15_3 (m.d 0 2) (by simp) with h19 | h19
                  · rcases p15_3 (m.d 1 2) (by simp) with h20 | h20
                    · linarith only [h0, h20, hlam]
                    · linarith only [h20, h7, hlam]
                  · linarith only [h19, hlam, p15_0]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h0, h10, h11, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h0, hlam, p15_1]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [hlam, p15_0]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h10, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15_1]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h0, h10, h11, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h1, hlam, p15_0]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h6, hlam, p15_0]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [hlam, p15_0]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h11, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p15_1]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h11, hlam, p15_1]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h2, hlam, p15_0]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h7, hlam, p15_0]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h10, hlam, p15_0]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [hlam, p15_0]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h13, hlam, p15_0]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h3, hlam, p15_0]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h8, hlam, p15_0]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [h0, h10, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                · have p15_0 := h15c.1
                  have p15_1 := h15c.2.1
                  have p15_2 := h15c.2.2.1
                  have p15_3 := h15c.2.2.2
                  linarith only [hlam, p15_0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
            · linarith only [h0, h1, h10, h4, h45, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
              · linarith only [h0, h47, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases h2bigk with h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht5b, p49_1, u5ehi1]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  rcases p49_3 (m.d 0 2) (by simp) with h52 | h52
                  · rcases p49_3 (m.d 1 2) (by simp) with h53 | h53
                    · linarith only [h0, h53, hlam]
                    · linarith only [h53, h6, hlam]
                  · linarith only [h52, hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  rcases p49_3 (m.d 0 2) (by simp) with h57 | h57
                  · rcases p49_3 (m.d 1 2) (by simp) with h58 | h58
                    · linarith only [h0, h58, hlam]
                    · linarith only [h58, h7, hlam]
                  · linarith only [h57, hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p49_1, u5ehi2]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h0, hlam, p49_1]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p49_1]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p49_1]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p49_1, u5ehi2]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h1, hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h6, hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h10, hlam, p49_1]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h45, hlam, p49_1]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h2, hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h7, hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h0, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p49_1]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h47, hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h3, hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h8, hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p49_1]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h0, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p49_1]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [hlam, p49_0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
          · linarith only [h0, h6, h83, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h85 | h85
            · linarith only [h0, h1, h4, h6, h85, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
              · linarith only [h0, h7, h87, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases h2bigk with h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht5b, p89_1, u5ehi2]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  rcases p89_3 (m.d 0 2) (by simp) with h92 | h92
                  · rcases p89_3 (m.d 1 2) (by simp) with h93 | h93
                    · linarith only [h0, h93, hlam]
                    · linarith only [h6, h93, hlam]
                  · linarith only [h92, hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  rcases p89_3 (m.d 0 2) (by simp) with h97 | h97
                  · rcases p89_3 (m.d 1 2) (by simp) with h98 | h98
                    · linarith only [h0, h98, hlam]
                    · linarith only [h7, h98, hlam]
                  · linarith only [h97, hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p89_1, u5ehi2]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h0, hlam, p89_1]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p89_1]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p89_1, u5ehi2]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h1, hlam, p89_0]
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
                  linarith only [h83, hlam, p89_1]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h85, hlam, p89_1]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h2, hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h7, hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h0, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h87, hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h3, hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h8, hlam, p89_0]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [h0, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p89_1]
                · have p89_0 := h89c.1
                  have p89_1 := h89c.2.1
                  have p89_2 := h89c.2.2.1
                  have p89_3 := h89c.2.2.2
                  linarith only [hlam, p89_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h123 | h123
        · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
          · linarith only [h0, h124, h3, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h123, h124, h3, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h127 | h127
          · linarith only [h0, h123, h127, h3, h6, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h129 | h129
            · linarith only [h0, h127, h129, h3, h7, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h131 | h131
              · linarith only [h0, h131, h3, h7, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases h2bigk with h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [hlam, p133_0]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [h0, h127, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p133_1]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  rcases p133_3 (m.d 0 2) (by simp) with h136 | h136
                  · rcases p133_3 (m.d 1 2) (by simp) with h137 | h137
                    · linarith only [h0, h137, hlam]
                    · linarith only [h137, h6, hlam]
                  · linarith only [h136, hlam, p133_0]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  rcases p133_3 (m.d 0 2) (by simp) with h141 | h141
                  · rcases p133_3 (m.d 1 2) (by simp) with h142 | h142
                    · linarith only [h0, h142, hlam]
                    · linarith only [h142, h7, hlam]
                  · linarith only [h141, hlam, p133_0]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p133_1, u5ehi2]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [h0, hlam, p133_1]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [hlam, p133_0]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p133_1]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [h0, h127, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p133_1]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [h8, hlam, p133_0]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [h1, hlam, p133_0]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [h6, hlam, p133_0]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [hlam, p133_0]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [h127, hlam, p133_1]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [h129, hlam, p133_1]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [h2, hlam, p133_0]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [h7, hlam, p133_0]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [h0, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p133_1]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [hlam, p133_0]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [h131, hlam, p133_0]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [h3, hlam, p133_0]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p133_1]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p133_1]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [h0, h1, h127, h131, h4, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p133_1]
                · have p133_0 := h133c.1
                  have p133_1 := h133c.2.1
                  have p133_2 := h133c.2.2.1
                  have p133_3 := h133c.2.2.2
                  linarith only [hlam, p133_0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h167 | h167
      · linarith only [h0, h167, h2, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h169 | h169
        · linarith only [h169, h6, h7, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h171 | h171
          · linarith only [h169, h171, h6, h7, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h173 | h173
            · linarith only [h167, h173, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h175 | h175
              · rcases h2bigk with h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [hlam, p176_0]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p176_1]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  rcases p176_3 (m.d 0 2) (by simp) with h179 | h179
                  · rcases p176_3 (m.d 1 2) (by simp) with h180 | h180
                    · linarith only [h0, h180, hlam]
                    · linarith only [h180, h6, hlam]
                  · linarith only [h179, hlam, p176_0]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h0, h175, hc01, hlam, hphi, ht0b, ht5b, p176_1, u5ehi2]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p176_1, u5ehi2]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h0, hlam, p176_1]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [hlam, p176_0]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p176_1]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h7, hlam, p176_0]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h167, hlam, p176_0]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h1, hlam, p176_0]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h6, hlam, p176_0]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [hlam, p176_0]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h171, hlam, p176_1]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h173, hlam, p176_1]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h2, hlam, p176_0]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p176_1]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h0, h1, h171, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p176_1]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [hlam, p176_0]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h0, h1, h167, h171, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p176_1]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h3, hlam, p176_0]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p176_1]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p176_1]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [h175, hlam, p176_1]
                · have p176_0 := h176c.1
                  have p176_1 := h176c.2.1
                  have p176_2 := h176c.2.2.1
                  have p176_3 := h176c.2.2.2
                  linarith only [hlam, p176_0]
              · linarith only [h0, h1, h175, h4, h5, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h207 | h207
    · rcases m.htr 1 2 5 (by decide) (by decide) with h208 | h208
      · linarith only [h0, h1, h208, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h210 | h210
        · rcases m.htr 2 3 4 (by decide) (by decide) with h211 | h211
          · rcases m.htr 2 3 5 (by decide) (by decide) with h212 | h212
            · rcases m.htr 2 4 5 (by decide) (by decide) with h213 | h213
              · linarith only [h0, h1, h207, h208, h212, h213, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases h2bigk with h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [hlam, p215_0]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h0, h207, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p215_1]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h0, h212, hc01, hlam, hphi, ht0b, ht5b, p215_1, u5ehi3]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  rcases p215_3 (m.d 0 2) (by simp) with h219 | h219
                  · rcases p215_3 (m.d 1 2) (by simp) with h220 | h220
                    · linarith only [h0, h220, hlam]
                    · linarith only [h207, h220, hlam]
                  · linarith only [h219, hlam, p215_0]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p215_1, u5ehi2]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h0, hlam, p215_1]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [hlam, p215_0]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h6, hlam, p215_0]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h0, h211, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p215_1]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h208, hlam, p215_0]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h1, hlam, p215_0]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p215_1]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [hlam, p215_0]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h0, h1, h211, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p215_1]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h0, h1, h207, h208, h211, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p215_1]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h2, hlam, p215_0]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h207, hlam, p215_0]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h211, hlam, p215_0]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [hlam, p215_0]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h213, hlam, p215_0]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h3, hlam, p215_0]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h207, h211, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p215_1]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h212, hlam, p215_0]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [h0, h1, h211, h213, h4, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p215_1]
                · have p215_0 := h215c.1
                  have p215_1 := h215c.2.1
                  have p215_2 := h215c.2.2.1
                  have p215_3 := h215c.2.2.2
                  linarith only [hlam, p215_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h245 | h245
              · linarith only [h0, h207, h245, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases h2bigk with h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [hlam, p247_0]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h0, h207, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p247_1]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h0, h207, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p247_1]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  rcases p247_3 (m.d 0 2) (by simp) with h251 | h251
                  · rcases p247_3 (m.d 1 2) (by simp) with h252 | h252
                    · linarith only [h0, h252, hlam]
                    · linarith only [h207, h252, hlam]
                  · linarith only [h251, hlam, p247_0]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p247_1, u5ehi2]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h0, hlam, p247_1]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [hlam, p247_0]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h6, hlam, p247_0]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h211, h212, h6, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p247_1]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h208, hlam, p247_0]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h1, hlam, p247_0]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h212, hc12, hc35, hlam, hphi, ht23, p247_1]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [hlam, p247_0]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h211, h212, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p247_1]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h212, hlam, p247_1]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h2, hlam, p247_0]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h207, hlam, p247_0]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h211, hlam, p247_0]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [hlam, p247_0]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h245, hlam, p247_0]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h3, hlam, p247_0]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h207, h211, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p247_1]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p247_1]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [h0, h1, h211, h245, h4, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p247_1]
                · have p247_0 := h247c.1
                  have p247_1 := h247c.2.1
                  have p247_2 := h247c.2.2.1
                  have p247_3 := h247c.2.2.2
                  linarith only [hlam, p247_0]
          · linarith only [h0, h1, h207, h211, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h207, h210, h6, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h279 | h279
      · linarith only [h0, h2, h207, h279, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h281 | h281
        · rcases m.htr 2 3 4 (by decide) (by decide) with h282 | h282
          · rcases m.htr 2 3 5 (by decide) (by decide) with h283 | h283
            · rcases m.htr 2 4 5 (by decide) (by decide) with h284 | h284
              · rcases h2bigk with h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  rcases p285_3 (m.d 0 2) (by simp) with h287 | h287
                  · rcases p285_3 (m.d 1 2) (by simp) with h288 | h288
                    · linarith only [h0, h288, hlam]
                    · rcases p285_3 (m.d 2 3) (by simp) with h290 | h290
                      · linarith only [h1, h290, hlam]
                      · linarith only [h290, h6, hlam]
                  · linarith only [h0, h287, hlam]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h0, h282, h284, hc01, hlam, hphi, ht0b, ht5b, p285_1, u5ehi2]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h0, h284, hc01, hlam, hphi, ht0b, ht5b, p285_1, u5ehi4]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p285_1, u5ehi2]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h0, hlam, p285_1]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h6, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h207, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h279, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h1, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p285_1]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h0, h1, h284, hc01, hlam, hphi, ht0b, ht5b, p285_1, u5ehi4]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h0, h1, h279, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p285_1]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h2, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p285_1]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h282, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h0, h1, h279, h282, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p285_1]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h3, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p285_1]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h283, hlam, p285_0]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [h284, hlam, p285_1]
                · have p285_0 := h285c.1
                  have p285_1 := h285c.2.1
                  have p285_2 := h285c.2.2.1
                  have p285_3 := h285c.2.2.2
                  linarith only [hlam, p285_0]
              · rcases h2bigk with h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  rcases p317_3 (m.d 0 2) (by simp) with h319 | h319
                  · rcases p317_3 (m.d 1 2) (by simp) with h320 | h320
                    · linarith only [h0, h320, hlam]
                    · rcases p317_3 (m.d 2 3) (by simp) with h322 | h322
                      · linarith only [h1, h322, hlam]
                      · linarith only [h322, h6, hlam]
                  · linarith only [h0, h319, hlam]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h0, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h0, h207, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h0, h279, hc01, hlam, hphi, ht0b, ht5b, p317_1, u5ehi1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h0, hlam, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h6, hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h207, hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h279, hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h1, hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h0, h1, h207, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h0, h1, h279, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h2, hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h282, hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h284, hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h3, hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h283, hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h0, h1, h284, h4, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [hlam, p317_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h349 | h349
              · linarith only [h282, h283, h349, hlam]
              · rcases h2bigk with h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [hlam, p351_0]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  rcases p351_3 (m.d 0 2) (by simp) with h353 | h353
                  · rcases p351_3 (m.d 1 2) (by simp) with h354 | h354
                    · linarith only [h0, h354, hlam]
                    · rcases p351_3 (m.d 2 3) (by simp) with h356 | h356
                      · linarith only [h1, h356, hlam]
                      · linarith only [h356, h6, hlam]
                  · linarith only [h0, h353, hlam]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [h0, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p351_1]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [h0, h207, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p351_1]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p351_1, u5ehi2]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [h0, hlam, p351_1]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [hlam, p351_0]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [h6, hlam, p351_0]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [h207, hlam, p351_0]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [h279, hlam, p351_0]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [h1, hlam, p351_0]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p351_1]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [hlam, p351_0]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [h0, h1, h207, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p351_1]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [h283, hlam, p351_1]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [h2, hlam, p351_0]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p351_1]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [h282, hlam, p351_0]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [hlam, p351_0]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [h349, hlam, p351_0]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [h3, hlam, p351_0]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p351_1]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p351_1]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [h0, h1, h207, h349, h4, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p351_1]
                · have p351_0 := h351c.1
                  have p351_1 := h351c.2.1
                  have p351_2 := h351c.2.2.1
                  have p351_3 := h351c.2.2.2
                  linarith only [hlam, p351_0]
          · linarith only [h281, h282, h6, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h384 | h384
          · rcases m.htr 2 3 5 (by decide) (by decide) with h385 | h385
            · rcases m.htr 2 4 5 (by decide) (by decide) with h386 | h386
              · rcases h2bigk with h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [hlam, p387_0]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  rcases p387_3 (m.d 0 2) (by simp) with h389 | h389
                  · rcases p387_3 (m.d 1 2) (by simp) with h390 | h390
                    · linarith only [h0, h390, hlam]
                    · rcases p387_3 (m.d 2 3) (by simp) with h392 | h392
                      · linarith only [h1, h392, hlam]
                      · linarith only [h392, h6, hlam]
                  · linarith only [h0, h389, hlam]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [h0, h281, h384, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p387_1]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [h0, h386, hc01, hlam, hphi, ht0b, ht5b, p387_1, u5ehi4]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p387_1, u5ehi2]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [h0, hlam, p387_1]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [hlam, p387_0]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [h6, hlam, p387_0]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [h207, hlam, p387_0]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [h279, hlam, p387_0]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [h1, hlam, p387_0]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p387_1]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [hlam, p387_0]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [h0, h1, h386, hc01, hlam, hphi, ht0b, ht5b, p387_1, u5ehi4]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [h0, h1, h279, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p387_1]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [h2, hlam, p387_0]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p387_1]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [h384, hlam, p387_0]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [hlam, p387_0]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [h0, h1, h279, h384, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p387_1]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [h3, hlam, p387_0]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p387_1]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [h385, hlam, p387_0]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [h386, hlam, p387_1]
                · have p387_0 := h387c.1
                  have p387_1 := h387c.2.1
                  have p387_2 := h387c.2.2.1
                  have p387_3 := h387c.2.2.2
                  linarith only [hlam, p387_0]
              · rcases h2bigk with h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [hlam, p419_0]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  rcases p419_3 (m.d 0 2) (by simp) with h421 | h421
                  · rcases p419_3 (m.d 1 2) (by simp) with h422 | h422
                    · linarith only [h0, h422, hlam]
                    · rcases p419_3 (m.d 2 3) (by simp) with h424 | h424
                      · linarith only [h1, h424, hlam]
                      · linarith only [h424, h6, hlam]
                  · linarith only [h0, h421, hlam]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [h0, h385, hc01, hlam, hphi, ht0b, ht5b, p419_1, u5ehi3]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [h0, h207, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p419_1, u5ehi2]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [h0, hlam, p419_1]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [hlam, p419_0]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [h6, hlam, p419_0]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [h207, hlam, p419_0]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [h279, hlam, p419_0]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [h1, hlam, p419_0]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p419_1]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [hlam, p419_0]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [h0, h1, h207, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [h0, h1, h279, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [h2, hlam, p419_0]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p419_1]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [h384, hlam, p419_0]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [hlam, p419_0]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [h386, hlam, p419_0]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [h3, hlam, p419_0]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p419_1]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [h385, hlam, p419_0]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [h0, h1, h386, h4, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p419_1]
                · have p419_0 := h419c.1
                  have p419_1 := h419c.2.1
                  have p419_2 := h419c.2.2.1
                  have p419_3 := h419c.2.2.2
                  linarith only [hlam, p419_0]
            · linarith only [h281, h384, h385, h6, hc12, hc35, hlam, hphi, ht23]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h452 | h452
            · linarith only [h0, h1, h384, h4, h452, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h454 | h454
              · rcases h2bigk with h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [hlam, p455_0]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  rcases p455_3 (m.d 0 2) (by simp) with h457 | h457
                  · rcases p455_3 (m.d 1 2) (by simp) with h458 | h458
                    · linarith only [h0, h458, hlam]
                    · rcases p455_3 (m.d 2 3) (by simp) with h460 | h460
                      · linarith only [h1, h460, hlam]
                      · linarith only [h460, h6, hlam]
                  · linarith only [h0, h457, hlam]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [h0, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p455_1]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [h0, h454, hc01, hlam, hphi, ht0b, ht5b, p455_1, u5ehi2]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p455_1, u5ehi2]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [h0, hlam, p455_1]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [hlam, p455_0]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [h6, hlam, p455_0]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [h207, hlam, p455_0]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [h279, hlam, p455_0]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [h1, hlam, p455_0]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p455_1]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [hlam, p455_0]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [h384, hlam, p455_1]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [h452, hlam, p455_1]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [h2, hlam, p455_0]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p455_1]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [h0, h1, h384, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p455_1]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [hlam, p455_0]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [h0, h1, h384, h4, h452, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p455_1]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [h3, hlam, p455_0]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p455_1]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [h0, h3, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p455_1]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [h454, hlam, p455_1]
                · have p455_0 := h455c.1
                  have p455_1 := h455c.2.1
                  have p455_2 := h455c.2.2.1
                  have p455_3 := h455c.2.2.2
                  linarith only [hlam, p455_0]
              · rcases h2bigk with h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  rcases p487_3 (m.d 0 2) (by simp) with h489 | h489
                  · rcases p487_3 (m.d 1 2) (by simp) with h490 | h490
                    · linarith only [h0, h490, hlam]
                    · rcases p487_3 (m.d 2 3) (by simp) with h492 | h492
                      · linarith only [h1, h492, hlam]
                      · linarith only [h492, h6, hlam]
                  · linarith only [h0, h489, hlam]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h0, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p487_1]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h0, h207, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p487_1]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p487_1, u5ehi2]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h0, hlam, p487_1]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h6, hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h207, hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h279, hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h1, hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p487_1]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h384, hlam, p487_1]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h452, hlam, p487_1]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h2, hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p487_1]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h0, h1, h384, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p487_1]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h454, hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h3, hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p487_1]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h0, h3, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p487_1]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h0, h1, h4, h454, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p487_1]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [hlam, p487_0]

end R2N4
