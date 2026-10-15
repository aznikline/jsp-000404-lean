import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_15_H_I_L_R_L_R_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
            · linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h5, h6, h8, hlam]
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
                  linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p10_1, u5ehi1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi2]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi3]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h5, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi3]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, hlam, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h5, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10_1, u3ehi3]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi3]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h5, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi3]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h1, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h1, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi3]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h1, h5, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi3]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h1, h4, h6, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10_1, u3ehi0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h3, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h5, hlam, p10_0]
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
                  linarith only [h2, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h4, hlam, p10_0]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u3ehi3]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [h0, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p10_1]
                · have p10_0 := h10c.1
                  have p10_1 := h10c.2.1
                  have p10_2 := h10c.2.2.1
                  have p10_3 := h10c.2.2.2
                  linarith only [hlam, p10_0]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
            · linarith only [h0, h3, h36, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h38 | h38
              · linarith only [h36, h38, h5, hc34, hlam, hphi, u3ehi2]
              · linarith only [h38, h5, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
          · linarith only [h0, h2, h3, h4, h41, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
          · linarith only [h0, h2, h3, h4, h41, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
        · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
          · linarith only [h0, h1, h3, h44, h45, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
            · rcases m.htr 3 4 5 (by decide) (by decide) with h48 | h48
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
                  linarith only [h0, h44, h47, hc01, hlam, hphi, ht0b, ht5b, p49_1, u5ehi4]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h0, h3, h44, h45, h47, hc01, hc34, hlam, hphi, ht0b, ht5b, p49_1, u3ehi2, u5ehi4]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h0, h3, h44, h47, hc01, hlam, hphi, ht0b, ht5b, p49_1, u5ehi4]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h0, h47, hc01, hlam, hphi, ht0b, ht5b, p49_1, u5ehi4]
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
                  linarith only [h3, h45, hc34, hlam, hphi, p49_1, u3ehi2]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h3, hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h3, h45, h47, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p49_1, u5ehi4]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h1, hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p49_1]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h45, hlam, p49_1]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h45, h47, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p49_1, u5ehi4]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h45, hc02, hc34, hlam, hphi, ht23, p49_1]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h44, h45, h47, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p49_1, u5ehi4]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h45, hc34, hlam, hphi, p49_1, u3ehi2]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h45, h47, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p49_1, u5ehi4]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h2, hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h44, hlam, p49_0]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h44, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p49_1, u3ehi2]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [h47, hlam, p49_1]
                · have p49_0 := h49c.1
                  have p49_1 := h49c.2.1
                  have p49_2 := h49c.2.2.1
                  have p49_3 := h49c.2.2.2
                  linarith only [hlam, p49_0]
              · linarith only [h3, h44, h45, h47, h48, hlam]
            · linarith only [h3, h44, h47, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
          · rcases m.htr 2 4 5 (by decide) (by decide) with h78 | h78
            · rcases m.htr 3 4 5 (by decide) (by decide) with h79 | h79
              · linarith only [h0, h1, h77, h79, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · linarith only [h0, h1, h77, h78, h79, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h82 | h82
              · linarith only [h3, h78, h82, hc12, hc34, hlam, hphi, ht23]
              · rcases h2bigk with h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [hlam, p84_0]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  rcases p84_3 (m.d 0 2) (by simp) with h86 | h86
                  · rcases p84_3 (m.d 1 2) (by simp) with h87 | h87
                    · linarith only [h0, h87, hlam]
                    · rcases p84_3 (m.d 2 3) (by simp) with h89 | h89
                      · linarith only [h1, h89, hlam]
                      · linarith only [h3, h78, h89, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h0, h86, hlam]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p84_1, u3ehi2]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [h0, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p84_1]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p84_1, u5ehi2]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [h0, hlam, p84_1]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [hlam, p84_0]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [h77, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p84_1, u3ehi3]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [h3, hlam, p84_0]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [h44, hlam, p84_0]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [h1, hlam, p84_0]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p84_1]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [hlam, p84_0]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [h0, h1, h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p84_1]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [h0, h1, h44, hc01, hlam, hphi, ht0b, ht5b, p84_1, u5ehi1]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [hc02, hc24, hlam, hphi, p84_1]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [h0, h2, h78, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p84_1]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [h77, hlam, p84_0]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [hlam, p84_0]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [h78, hlam, p84_0]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [h2, hlam, p84_0]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [h0, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p84_1]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [h0, h2, h77, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p84_1, u3ehi3]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [h0, h2, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p84_1]
                · have p84_0 := h84c.1
                  have p84_1 := h84c.2.1
                  have p84_2 := h84c.2.2.1
                  have p84_3 := h84c.2.2.2
                  linarith only [hlam, p84_0]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h116 | h116
            · rcases m.htr 3 4 5 (by decide) (by decide) with h117 | h117
              · rcases h2bigk with h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [hlam, p118_0]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  rcases p118_3 (m.d 0 2) (by simp) with h120 | h120
                  · rcases p118_3 (m.d 1 2) (by simp) with h121 | h121
                    · linarith only [h0, h121, hlam]
                    · rcases p118_3 (m.d 2 3) (by simp) with h123 | h123
                      · linarith only [h1, h123, hlam]
                      · linarith only [h0, h123, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p118_1, u3ehi2]
                  · linarith only [h0, h120, hlam]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p118_1, u3ehi2]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h0, h116, hc01, hlam, hphi, ht0b, ht5b, p118_1, u5ehi2]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p118_1, u5ehi2]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h0, hlam, p118_1]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [hlam, p118_0]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h2, h44, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p118_1, u3ehi2]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h3, hlam, p118_0]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h44, hlam, p118_0]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h1, hlam, p118_0]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p118_1]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [hlam, p118_0]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h77, hlam, p118_1]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h77, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p118_1, u5ehi2]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h77, hc02, hc34, hlam, hphi, ht23, p118_1]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h77, hc12, hc34, hlam, hphi, ht23, p118_1]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h77, hc34, hlam, hphi, p118_1, u3ehi2]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [hlam, p118_0]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h44, h77, hc12, hc34, hlam, hphi, ht23, p118_1]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h2, hlam, p118_0]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h2, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p118_1]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p118_1, u3ehi2]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [h116, hlam, p118_1]
                · have p118_0 := h118c.1
                  have p118_1 := h118c.2.1
                  have p118_2 := h118c.2.2.1
                  have p118_3 := h118c.2.2.2
                  linarith only [hlam, p118_0]
              · linarith only [h117, h77, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h151 | h151
              · linarith only [h116, h151, h3, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h151, h77, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h154 | h154
      · rcases m.htr 1 2 5 (by decide) (by decide) with h155 | h155
        · linarith only [h0, h155, h2, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h157 | h157
          · linarith only [h1, h157, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h159 | h159
            · linarith only [h0, h154, h159, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · linarith only [h0, h154, h157, h159, h2, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h162 | h162
        · linarith only [h0, h162, h2, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h164 | h164
          · linarith only [h1, h164, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h166 | h166
            · linarith only [h1, h164, h166, h2, hc34, hlam, hphi, u3ehi2]
            · linarith only [h1, h166, h2, hc45, hlam, hphi, ht34, u3ehi2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h169 | h169
    · rcases m.htr 1 2 4 (by decide) (by decide) with h170 | h170
      · rcases m.htr 1 2 5 (by decide) (by decide) with h171 | h171
        · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
          · rcases m.htr 2 4 5 (by decide) (by decide) with h173 | h173
            · linarith only [h0, h170, h173, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h175 | h175
              · linarith only [h172, h173, h175, hlam]
              · rcases h2bigk with h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [hlam, p177_0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h1, hc12, hc23, hlam, hphi, p177_1]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h1, hlam, p177_0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h1, h172, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p177_1, u3ehi3]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h1, h172, h173, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p177_1, u3ehi3]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h0, hlam, p177_1]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [hlam, p177_0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h1, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p177_1]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h0, h1, h172, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p177_1, u3ehi3]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h0, h1, h172, h173, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p177_1, u3ehi3]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [hc02, hc23, hlam, hphi, p177_1]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h171, h172, h173, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p177_1, u3ehi3]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [hlam, p177_0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h172, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p177_1, u3ehi3]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h172, h173, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p177_1, u3ehi3]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h0, h171, h173, hlam, p177_1]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h170, hlam, p177_0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h172, hlam, p177_0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [hlam, p177_0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h173, hlam, p177_0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h169, hlam, p177_0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h171, hlam, p177_0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h0, h171, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p177_1, u3ehi2]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h169, h172, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p177_1, u3ehi3]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [hlam, p177_0]
          · linarith only [h0, h1, h171, h172, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
        · linarith only [h1, h169, h171, hc12, hc23, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h205 | h205
        · rcases m.htr 2 3 4 (by decide) (by decide) with h206 | h206
          · rcases m.htr 2 4 5 (by decide) (by decide) with h207 | h207
            · rcases m.htr 3 4 5 (by decide) (by decide) with h208 | h208
              · rcases h2bigk with h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [hlam, p209_0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h1, h205, h207, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p209_1, u5ehi4]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h1, hlam, p209_0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h1, h170, h205, h207, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p209_1, u5ehi4]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h1, h207, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p209_1, u5ehi4]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h0, hlam, p209_1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [hlam, p209_0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h1, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p209_1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h170, hlam, p209_0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h0, h1, h207, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p209_1, u5ehi4]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [hc02, hc23, hlam, hphi, p209_1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h205, h207, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p209_1, u5ehi4]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [hlam, p209_0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h170, h205, h207, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p209_1, u5ehi4]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h207, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p209_1, u5ehi4]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h0, h205, h207, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p209_1, u5ehi4]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h205, h207, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p209_1, u5ehi4]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h206, hlam, p209_0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [hlam, p209_0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h206, h207, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p209_1, u5ehi4]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h169, hlam, p209_0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h205, hlam, p209_0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h0, h1, h205, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p209_1, u3ehi0]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [h207, hlam, p209_1]
                · have p209_0 := h209c.1
                  have p209_1 := h209c.2.1
                  have p209_2 := h209c.2.2.1
                  have p209_3 := h209c.2.2.2
                  linarith only [hlam, p209_0]
              · linarith only [h0, h1, h205, h207, h208, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h170, h205, h207, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
          · linarith only [h0, h1, h205, h206, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
        · linarith only [h1, h169, h205, hc12, hc23, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h239 | h239
      · rcases m.htr 1 2 5 (by decide) (by decide) with h240 | h240
        · linarith only [h0, h169, h240, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h242 | h242
          · rcases m.htr 2 4 5 (by decide) (by decide) with h243 | h243
            · linarith only [h0, h169, h239, h243, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · linarith only [h0, h169, h239, h242, h243, hc45, hlam, hphi, ht34, u3ehi3]
          · linarith only [h0, h1, h239, h242, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h247 | h247
        · linarith only [h0, h169, h247, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h249 | h249
          · rcases m.htr 2 4 5 (by decide) (by decide) with h250 | h250
            · rcases m.htr 3 4 5 (by decide) (by decide) with h251 | h251
              · rcases h2bigk with h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [hlam, p252_0]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [h169, h249, h250, hc12, hc23, hlam, hphi, p252_1]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [h1, hlam, p252_0]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [h169, h250, hlam, p252_1]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [h169, hlam, p252_0]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [h0, hlam, p252_1]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [hlam, p252_0]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [h169, h249, h250, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p252_1]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [h239, hlam, p252_0]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [h247, hlam, p252_0]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [h0, hc12, hc23, hlam, hphi, p252_1]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p252_1]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [hlam, p252_0]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [h249, h251, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p252_1, u5ehi4]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [h0, h169, hc12, hc23, hlam, hphi, p252_1]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [h0, hc12, hc24, hlam, hphi, p252_1]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p252_1]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [h249, hlam, p252_0]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [hlam, p252_0]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [h0, h169, h249, hc12, hc23, hlam, hphi, p252_1]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [h0, hc12, hc25, hlam, hphi, p252_1]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p252_1]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [h249, h250, hlam, p252_1]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [h250, hlam, p252_1]
                · have p252_0 := h252c.1
                  have p252_1 := h252c.2.1
                  have p252_2 := h252c.2.2.1
                  have p252_3 := h252c.2.2.2
                  linarith only [hlam, p252_0]
              · rcases h2bigk with h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [hlam, p278_0]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [h1, hc12, hc23, hlam, hphi, p278_1]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [h1, hlam, p278_0]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [h169, h250, hlam, p278_1]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [h169, hlam, p278_0]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [h0, hlam, p278_1]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [hlam, p278_0]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [h169, h249, h250, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p278_1]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [h239, hlam, p278_0]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [h247, hlam, p278_0]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [h0, hc12, hc23, hlam, hphi, p278_1]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p278_1]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [hlam, p278_0]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [h250, h251, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p278_1, u3ehi3]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [h250, h251, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p278_1, u3ehi3]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [h0, hc12, hc24, hlam, hphi, p278_1]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p278_1]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [h249, hlam, p278_0]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [hlam, p278_0]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [h249, h250, h251, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p278_1, u3ehi3]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [h0, hc12, hc25, hlam, hphi, p278_1]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p278_1]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [h249, h250, hlam, p278_1]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [h250, hlam, p278_1]
                · have p278_0 := h278c.1
                  have p278_1 := h278c.2.1
                  have p278_2 := h278c.2.2.1
                  have p278_3 := h278c.2.2.2
                  linarith only [hlam, p278_0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h304 | h304
              · linarith only [h239, h250, h304, hc12, hc34, hlam, hphi, ht23]
              · rcases h2bigk with h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [hlam, p306_0]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [h1, hc12, hc23, hlam, hphi, p306_1]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [h1, hlam, p306_0]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [h239, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p306_1]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [h169, hlam, p306_0]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [h0, hlam, p306_1]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [hlam, p306_0]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p306_1, u3ehi0]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [h239, hlam, p306_0]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [h247, hlam, p306_0]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [hc02, hc23, hlam, hphi, p306_1]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p306_1]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [hlam, p306_0]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [h249, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p306_1, u3ehi3]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p306_1, u5ehi2]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [h0, hc12, hc24, hlam, hphi, p306_1]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p306_1]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [h249, hlam, p306_0]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [hlam, p306_0]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [h250, hlam, p306_0]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [h0, hc12, hc25, hlam, hphi, p306_1]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p306_1]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [h250, hc45, hlam, hphi, ht34, p306_1, u3ehi2]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [h239, h250, hc14, hc45, hlam, hphi, p306_1]
                · have p306_0 := h306c.1
                  have p306_1 := h306c.2.1
                  have p306_2 := h306c.2.2.1
                  have p306_3 := h306c.2.2.2
                  linarith only [hlam, p306_0]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h332 | h332
            · rcases m.htr 3 4 5 (by decide) (by decide) with h333 | h333
              · rcases h2bigk with h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [hlam, p334_0]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [h1, hc12, hc23, hlam, hphi, p334_1]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [h1, hlam, p334_0]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [h169, h332, hlam, p334_1]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [h169, hlam, p334_0]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [h0, hlam, p334_1]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [hlam, p334_0]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p334_1, u3ehi2]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [h239, hlam, p334_0]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [h247, hlam, p334_0]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [hc02, hc23, hlam, hphi, p334_1]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p334_1]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [hlam, p334_0]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [h249, hlam, p334_1]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [h249, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p334_1, u5ehi2]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [h0, hc12, hc24, hlam, hphi, p334_1]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p334_1]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [h249, hc34, hlam, hphi, p334_1, u3ehi2]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [hlam, p334_0]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [h0, h169, h249, hc12, hc34, hlam, hphi, ht23, p334_1]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [h0, hc12, hc25, hlam, hphi, p334_1]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p334_1]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [h0, h1, h249, h332, hc12, hc34, hlam, hphi, ht23, p334_1]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [h332, hlam, p334_1]
                · have p334_0 := h334c.1
                  have p334_1 := h334c.2.1
                  have p334_2 := h334c.2.2.1
                  have p334_3 := h334c.2.2.2
                  linarith only [hlam, p334_0]
              · linarith only [h0, h1, h249, h333, hc12, hc45, hlam, hphi, ht23, ht34]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h361 | h361
              · linarith only [h239, h332, h361, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h0, h1, h249, h361, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
