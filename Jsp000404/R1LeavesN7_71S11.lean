import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_14_H_I_L_R_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
            · linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h0, h5, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · rcases h2bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p10_1, u4ehi1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  rcases p10_3 (m.d 0 2) (by simp) with h13 | h13
                  · rcases p10_3 (m.d 1 2) (by simp) with h14 | h14
                    · linarith only [h0, h14, hlam]
                    · linarith only [h14, h4, hlam]
                  · linarith only [h13, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p10_1, u4ehi2]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p10_1, u4ehi2]
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
                  linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p10_1, u4ehi2]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p10_1, u4ehi2]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h1, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h4, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h6, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10_1, u4ehi2]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h2, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h5, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h8, hc23, hc45, hlam, hphi, ht34, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h8, hlam, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h3, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p10_1, u4ehi2]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
            · linarith only [h0, h2, h4, h40, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
              · rcases h2bigk with h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [hlam, p43_0]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  rcases p43_3 (m.d 0 2) (by simp) with h46 | h46
                  · rcases p43_3 (m.d 1 2) (by simp) with h47 | h47
                    · linarith only [h0, h47, hlam]
                    · linarith only [h4, h47, hlam]
                  · linarith only [h46, hlam, p43_0]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p43_1, u4ehi2]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h0, h42, hc01, hlam, hphi, ht0b, ht45, ht5b, p43_1, u4ehi4]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h0, hlam, p43_0]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [hlam, p43_0]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p43_1]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h5, hlam, p43_0]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h0, h2, h42, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p43_1, u4ehi4]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h1, hlam, p43_0]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h4, hlam, p43_0]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [hlam, p43_0]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h40, hlam, p43_0]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h42, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p43_1, u4ehi4]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h2, hlam, p43_0]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h0, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p43_1]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h0, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [hlam, p43_0]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h0, h2, h42, hc01, hlam, hphi, ht0b, ht45, ht5b, p43_1, u4ehi4]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h3, hlam, p43_0]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h4, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p43_1]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h0, h2, h42, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [h42, hlam, p43_0]
                · have p43_0 := h43c.1
                  have p43_1 := h43c.2.1
                  have p43_2 := h43c.2.2.1
                  have p43_3 := h43c.2.2.2
                  linarith only [hlam, p43_0]
              · linarith only [h4, h42, h5, hc23, hc45, hlam, hphi, ht34]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
          · linarith only [h0, h1, h4, h74, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
            · rcases m.htr 2 4 5 (by decide) (by decide) with h77 | h77
              · rcases h2bigk with h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [hlam, p78_0]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  rcases p78_3 (m.d 0 2) (by simp) with h80 | h80
                  · rcases p78_3 (m.d 1 2) (by simp) with h81 | h81
                    · linarith only [h0, h81, hlam]
                    · rcases p78_3 (m.d 2 3) (by simp) with h83 | h83
                      · linarith only [h1, h83, hlam]
                      · linarith only [h4, h83, hlam]
                  · linarith only [h0, h80, hlam]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [h0, h76, hc01, hlam, hphi, ht0b, ht45, ht5b, p78_1, u4ehi2]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [h0, h77, hc01, hlam, hphi, ht0b, ht45, ht5b, p78_1, u4ehi4]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [h0, h77, hc01, hlam, hphi, ht0b, ht45, ht5b, p78_1, u4ehi4]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [h0, hlam, p78_0]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [hlam, p78_0]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [h4, hlam, p78_0]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [h74, hlam, p78_0]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [h77, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p78_1, u4ehi4]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [h1, hlam, p78_0]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p78_1]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [hlam, p78_0]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [h0, h1, h77, hc01, hlam, hphi, ht0b, ht45, ht5b, p78_1, u4ehi4]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [h0, h1, h77, hc01, hlam, hphi, ht0b, ht45, ht5b, p78_1, u4ehi4]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [h2, hlam, p78_0]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p78_1]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [h76, hlam, p78_1]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [hlam, p78_0]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [h0, h1, h76, h77, hc01, hlam, hphi, ht0b, ht45, ht5b, p78_1, u4ehi4]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [h3, hlam, p78_0]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p78_1]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [h76, h77, hlam, p78_1]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [h77, hlam, p78_0]
                · have p78_0 := h78c.1
                  have p78_1 := h78c.2.1
                  have p78_2 := h78c.2.2.1
                  have p78_3 := h78c.2.2.2
                  linarith only [hlam, p78_0]
              · rcases h2bigk with h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [hlam, p110_0]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  rcases p110_3 (m.d 0 2) (by simp) with h112 | h112
                  · rcases p110_3 (m.d 1 2) (by simp) with h113 | h113
                    · linarith only [h0, h113, hlam]
                    · rcases p110_3 (m.d 2 3) (by simp) with h115 | h115
                      · linarith only [h1, h115, hlam]
                      · linarith only [h115, h4, hlam]
                  · linarith only [h0, h112, hlam]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [h0, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p110_1]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p110_1, u4ehi2]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [h0, h74, h77, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p110_1]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [h0, hlam, p110_0]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [hlam, p110_0]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [h4, hlam, p110_0]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [h74, hlam, p110_0]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [h74, h77, hlam, p110_1]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [h1, hlam, p110_0]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p110_1]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [hlam, p110_0]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [h0, h1, h74, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p110_1]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [h0, h1, h74, h77, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p110_1]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [h2, hlam, p110_0]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p110_1]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [h76, hlam, p110_1]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [hlam, p110_0]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [h77, hlam, p110_1]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [h3, hlam, p110_0]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [h0, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p110_1]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p110_1]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p110_1, u4ehi2]
                · have p110_0 := h110c.1
                  have p110_1 := h110c.2.1
                  have p110_2 := h110c.2.2.1
                  have p110_3 := h110c.2.2.2
                  linarith only [hlam, p110_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h142 | h142
              · rcases h2bigk with h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [hlam, p143_0]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  rcases p143_3 (m.d 0 2) (by simp) with h145 | h145
                  · rcases p143_3 (m.d 1 2) (by simp) with h146 | h146
                    · linarith only [h0, h146, hlam]
                    · rcases p143_3 (m.d 2 3) (by simp) with h148 | h148
                      · linarith only [h1, h148, hlam]
                      · linarith only [h148, h4, hlam]
                  · linarith only [h0, h145, hlam]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [h0, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p143_1]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [h0, h142, hc01, hlam, hphi, ht0b, ht45, ht5b, p143_1, u4ehi4]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [h0, h142, hc01, hlam, hphi, ht0b, ht45, ht5b, p143_1, u4ehi4]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [h0, hlam, p143_0]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [hlam, p143_0]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [h4, hlam, p143_0]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [h74, hlam, p143_0]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [h142, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p143_1, u4ehi4]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [h1, hlam, p143_0]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p143_1]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [hlam, p143_0]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [h76, hlam, p143_0]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [h142, h76, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p143_1, u4ehi4]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [h2, hlam, p143_0]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p143_1]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [h0, h2, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p143_1]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [hlam, p143_0]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [h0, h142, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p143_1, u4ehi4]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [h3, hlam, p143_0]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p143_1]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [h0, h142, h2, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p143_1]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [h142, hlam, p143_0]
                · have p143_0 := h143c.1
                  have p143_1 := h143c.2.1
                  have p143_2 := h143c.2.2.1
                  have p143_3 := h143c.2.2.2
                  linarith only [hlam, p143_0]
              · rcases h2bigk with h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [hlam, p175_0]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  rcases p175_3 (m.d 0 2) (by simp) with h177 | h177
                  · rcases p175_3 (m.d 1 2) (by simp) with h178 | h178
                    · linarith only [h0, h178, hlam]
                    · rcases p175_3 (m.d 2 3) (by simp) with h180 | h180
                      · linarith only [h1, h180, hlam]
                      · linarith only [h180, h4, hlam]
                  · linarith only [h0, h177, hlam]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [h0, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p175_1, u4ehi2]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [h0, h142, h4, h76, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [h0, hlam, p175_0]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [hlam, p175_0]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [h4, hlam, p175_0]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [h74, hlam, p175_0]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [h142, h4, h76, hlam, p175_1]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [h1, hlam, p175_0]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p175_1]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [hlam, p175_0]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [h76, hlam, p175_0]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [h142, h76, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p175_1]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [h2, hlam, p175_0]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [h142, hc12, hc45, hlam, hphi, ht23, ht34, p175_1]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [h142, hc23, hc45, hlam, hphi, ht34, p175_1]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [hlam, p175_0]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [h142, hlam, p175_1]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [h3, hlam, p175_0]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p175_1]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [h0, h3, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p175_1, u4ehi2]
                · have p175_0 := h175c.1
                  have p175_1 := h175c.2.1
                  have p175_2 := h175c.2.2.1
                  have p175_3 := h175c.2.2.2
                  linarith only [hlam, p175_0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h207 | h207
        · rcases m.htr 1 2 4 (by decide) (by decide) with h208 | h208
          · rcases m.htr 2 3 4 (by decide) (by decide) with h209 | h209
            · linarith only [h0, h207, h209, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h211 | h211
              · linarith only [h0, h208, h211, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h0, h208, h211, h3, hc45, hlam, hphi, u4ehi2]
          · linarith only [h2, h208, h3, hc12, hc25, hlam, hphi]
        · linarith only [h1, h207, h3, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h216 | h216
      · rcases m.htr 1 2 3 (by decide) (by decide) with h217 | h217
        · rcases m.htr 1 2 4 (by decide) (by decide) with h218 | h218
          · linarith only [h0, h2, h216, h218, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h220 | h220
            · linarith only [h0, h2, h217, h220, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h222 | h222
              · rcases h2bigk with h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [hlam, p223_0]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h2, h220, hc12, hc34, hlam, hphi, ht23, p223_1]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h2, h220, hc23, hc34, hlam, hphi, p223_1]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h2, hlam, p223_0]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h2, h220, h222, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p223_1, u4ehi4]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h0, hlam, p223_0]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [hlam, p223_0]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p223_1]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h218, hlam, p223_0]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h0, h2, h220, h222, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p223_1, u4ehi4]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h1, hlam, p223_0]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h217, hlam, p223_0]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [hlam, p223_0]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h220, hlam, p223_0]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h222, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p223_1, u4ehi4]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h220, hc02, hc34, hlam, hphi, ht23, p223_1]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h217, h220, hc23, hc34, hlam, hphi, p223_1]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h220, hc23, hc34, hlam, hphi, p223_1]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [hlam, p223_0]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h220, h222, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p223_1, u4ehi4]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h216, hlam, p223_0]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h216, h217, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p223_1]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h2, h216, h220, hc23, hc34, hlam, hphi, p223_1]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [h222, hlam, p223_0]
                · have p223_0 := h223c.1
                  have p223_1 := h223c.2.1
                  have p223_2 := h223c.2.2.1
                  have p223_3 := h223c.2.2.2
                  linarith only [hlam, p223_0]
              · linarith only [h0, h2, h217, h222, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h1, h2, h217, hc12, hc24, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h251 | h251
        · rcases m.htr 1 2 4 (by decide) (by decide) with h252 | h252
          · linarith only [h0, h2, h252, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h254 | h254
            · linarith only [h0, h2, h251, h254, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h256 | h256
              · rcases h2bigk with h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [hlam, p257_0]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h216, h254, h256, hc12, hc34, hlam, hphi, ht23, p257_1]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h216, h254, h256, hc23, hc34, hlam, hphi, p257_1]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h2, hlam, p257_0]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h216, hlam, p257_0]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h0, hlam, p257_0]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [hlam, p257_0]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p257_1]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h252, hlam, p257_0]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h0, h216, hlam, p257_1]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h1, hlam, p257_0]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h251, hlam, p257_0]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [hlam, p257_0]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h254, hlam, p257_0]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h216, h251, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p257_1]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h1, h254, hc23, hc34, hlam, hphi, p257_1]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h251, h254, hc23, hc34, hlam, hphi, p257_1]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h254, hc23, hc34, hlam, hphi, p257_1]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [hlam, p257_0]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h0, h216, h251, h254, hc23, hc34, hlam, hphi, p257_1]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h0, h251, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p257_1]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h251, h254, h256, hc23, hc34, hlam, hphi, p257_1]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h254, h256, hc23, hc34, hlam, hphi, p257_1]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [h256, hlam, p257_0]
                · have p257_0 := h257c.1
                  have p257_1 := h257c.2.1
                  have p257_2 := h257c.2.2.1
                  have p257_3 := h257c.2.2.2
                  linarith only [hlam, p257_0]
              · linarith only [h0, h2, h251, h256, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h1, h2, h251, hc12, hc24, hlam, hphi]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h285 | h285
    · rcases m.htr 0 2 5 (by decide) (by decide) with h286 | h286
      · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
        · linarith only [h1, h285, h287, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h289 | h289
          · rcases m.htr 2 3 4 (by decide) (by decide) with h290 | h290
            · rcases m.htr 2 4 5 (by decide) (by decide) with h291 | h291
              · linarith only [h0, h1, h289, h291, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases h2bigk with h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [hlam, p293_0]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [h1, hc12, hc23, hlam, hphi, p293_1]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [h1, hlam, p293_0]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [h1, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p293_1, u4ehi2]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [h1, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p293_1]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [h0, hlam, p293_0]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [hlam, p293_0]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [h287, hlam, p293_0]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p293_1, u4ehi2]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [h0, h1, h290, h291, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p293_1, u4ehi3]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [hc02, hc23, hlam, hphi, p293_1]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p293_1]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [hlam, p293_0]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [h290, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p293_1, u4ehi3]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [h290, h291, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p293_1, u4ehi3]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [h285, hlam, p293_0]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [h289, hlam, p293_0]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [h290, hlam, p293_1]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [hlam, p293_0]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [h291, hlam, p293_1]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [h286, hlam, p293_0]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [h286, h289, h290, hc02, hlam, hphi, ht0b, ht45, ht5b, p293_1, u4ehi3]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [h1, h286, hlam, p293_1]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [h1, h286, h290, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p293_1, u4ehi3]
                · have p293_0 := h293c.1
                  have p293_1 := h293c.2.1
                  have p293_2 := h293c.2.2.1
                  have p293_3 := h293c.2.2.2
                  linarith only [hlam, p293_0]
            · linarith only [h0, h1, h289, h290, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
          · linarith only [h1, h285, h289, hc12, hc23, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h321 | h321
        · linarith only [h1, h285, h321, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h323 | h323
          · rcases m.htr 2 3 4 (by decide) (by decide) with h324 | h324
            · rcases m.htr 2 4 5 (by decide) (by decide) with h325 | h325
              · linarith only [h0, h1, h323, h325, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h0, h286, h323, h325, hc45, hlam, hphi, u4ehi2]
            · linarith only [h0, h1, h323, h324, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
          · linarith only [h1, h285, h323, hc12, hc23, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h330 | h330
      · rcases m.htr 1 2 3 (by decide) (by decide) with h331 | h331
        · linarith only [h0, h1, h330, h331, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h333 | h333
          · linarith only [h0, h285, h333, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h335 | h335
            · rcases m.htr 2 4 5 (by decide) (by decide) with h336 | h336
              · rcases h2bigk with h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [hlam, p337_0]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [h285, h335, hc12, hc23, hlam, hphi, p337_1]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [h1, hlam, p337_0]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [h285, hlam, p337_0]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [h285, h335, h336, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p337_1, u4ehi4]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [h0, hlam, p337_0]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [hlam, p337_0]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [h331, hlam, p337_0]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [h333, hlam, p337_0]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [h336, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p337_1, u4ehi4]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [hc02, hc23, hlam, hphi, p337_1]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p337_1]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [hlam, p337_0]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p337_1, u4ehi2]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [h336, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p337_1, u4ehi4]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [h330, h336, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p337_1, u4ehi4]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p337_1]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [h335, hlam, p337_1]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [hlam, p337_0]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [h335, h336, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p337_1, u4ehi4]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [h330, hlam, p337_0]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [h330, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p337_1]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [h285, h330, h335, hlam, p337_1]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [h336, hlam, p337_0]
                · have p337_0 := h337c.1
                  have p337_1 := h337c.2.1
                  have p337_2 := h337c.2.2.1
                  have p337_3 := h337c.2.2.2
                  linarith only [hlam, p337_0]
              · linarith only [h285, h330, h336, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h364 | h364
              · linarith only [h1, h330, h335, h364, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
              · linarith only [h1, h330, h335, h364, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h367 | h367
        · linarith only [h0, h1, h367, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h369 | h369
          · linarith only [h0, h285, h369, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h371 | h371
            · rcases m.htr 2 4 5 (by decide) (by decide) with h372 | h372
              · rcases h2bigk with h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [hlam, p373_0]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h330, hc12, hc25, hlam, hphi, p373_1]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h1, hlam, p373_0]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h285, hlam, p373_0]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h330, hlam, p373_0]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h0, hlam, p373_0]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [hlam, p373_0]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h367, hlam, p373_0]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h369, hlam, p373_0]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h330, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p373_1]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h0, hc12, hc23, hlam, hphi, p373_1]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p373_1]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [hlam, p373_0]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h372, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p373_1, u4ehi4]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h0, h330, hc12, hc23, hlam, hphi, p373_1]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h0, hc12, hc24, hlam, hphi, p373_1]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p373_1]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h371, hlam, p373_1]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [hlam, p373_0]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h0, h330, h371, hc12, hc23, hlam, hphi, p373_1]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h0, hc12, hc25, hlam, hphi, p373_1]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h371, h372, hc12, hc23, hlam, hphi, p373_1]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h371, h372, hlam, p373_1]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [h372, hlam, p373_0]
                · have p373_0 := h373c.1
                  have p373_1 := h373c.2.1
                  have p373_2 := h373c.2.2.1
                  have p373_3 := h373c.2.2.2
                  linarith only [hlam, p373_0]
              · rcases h2bigk with h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [hlam, p399_0]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [h1, hc12, hc23, hlam, hphi, p399_1]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [h1, hlam, p399_0]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [h285, hlam, p399_0]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [h330, hlam, p399_0]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [h0, hlam, p399_0]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [hlam, p399_0]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [h367, hlam, p399_0]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [h369, hlam, p399_0]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p399_1]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [hc02, hc23, hlam, hphi, p399_1]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p399_1]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [hlam, p399_0]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p399_1, u4ehi2]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [h0, h285, h372, hc12, hc23, hlam, hphi, p399_1]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [h0, hc12, hc24, hlam, hphi, p399_1]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [h372, hc12, hc25, hlam, hphi, p399_1]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [h371, hlam, p399_1]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [hlam, p399_0]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [h372, hlam, p399_1]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [h0, hc12, hc25, hlam, hphi, p399_1]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [h372, hc12, hc45, hlam, hphi, ht23, ht34, p399_1]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [h1, h372, hc03, hc45, hlam, hphi, ht34, p399_1]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [h372, hc45, hlam, hphi, p399_1, u4ehi2]
                · have p399_0 := h399c.1
                  have p399_1 := h399c.2.1
                  have p399_2 := h399c.2.2.1
                  have p399_3 := h399c.2.2.2
                  linarith only [hlam, p399_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h425 | h425
              · rcases h2bigk with h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h1, h371, hc12, hc34, hlam, hphi, ht23, p426_1]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h1, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h285, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h330, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h0, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h367, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h369, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p426_1]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h371, hc02, hc34, hlam, hphi, ht23, p426_1]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h371, hc12, hc34, hlam, hphi, ht23, p426_1]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h371, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h0, h330, h371, hc12, hc34, hlam, hphi, ht23, p426_1]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h0, h371, hc12, hc34, hlam, hphi, ht23, p426_1]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h371, hc12, hc34, hlam, hphi, ht23, p426_1]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h367, h371, hc13, hc34, hlam, hphi, p426_1]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h0, h330, h371, hc12, hc34, hlam, hphi, ht23, p426_1]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h0, hc12, hc25, hlam, hphi, p426_1]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h371, h425, hc12, hc34, hlam, hphi, ht23, p426_1]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h0, h1, h371, h425, hc12, hc34, hlam, hphi, ht23, p426_1]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h425, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hlam, p426_0]
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
                  linarith only [h1, hc12, hc23, hlam, hphi, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h1, hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h285, hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h330, hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h0, hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h367, hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h369, hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h371, h425, hc02, hc45, hlam, hphi, ht23, ht34, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h371, h425, hc12, hc45, hlam, hphi, ht23, ht34, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h371, hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h371, h425, hlam, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h0, h425, hc12, hc45, hlam, hphi, ht23, ht34, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h425, hc12, hc45, hlam, hphi, ht23, ht34, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h367, h425, hc13, hc45, hlam, hphi, ht34, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h425, hlam, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h0, hc12, hc25, hlam, hphi, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h425, hc12, hc45, hlam, hphi, ht23, ht34, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h0, h1, h425, hc12, hc45, hlam, hphi, ht23, ht34, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h425, hc45, hlam, hphi, p452_1, u4ehi2]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [hlam, p452_0]

end R2N4
