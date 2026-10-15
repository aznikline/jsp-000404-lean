import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3294000 in
set_option maxHeartbeats 3294000 in
theorem r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
      · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
            · rcases h0bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, p11_1, u5ehi4]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h7, h9, hc01, hlam, hphi, ht0b, ht5b, p11_1, u5ehi4]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h9, hc01, hlam, hphi, ht0b, ht5b, p11_1, u5ehi4]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p11_1, u5ehi0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h0, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h7, h9, hc02, hlam, hphi, ht0b, ht5b, p11_1, u5ehi4]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h9, hlam, hphi, ht01, ht0b, ht12, ht5b, p11_1, u2elo0, u5ehi4]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h3, hlam, hphi, ht01, ht0b, ht12, ht5b, p11_1, u2elo0, u5ehi1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h1, hlam, p11_1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h4, hlam, p11_1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h9, hc03, hlam, hphi, ht0b, ht5b, p11_1, u5ehi4]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, p11_1, u2elo0, u5ehi1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h2, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h5, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h7, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h3, hc04, hlam, hphi, ht0b, ht5b, p11_1, u5ehi1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h3, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h6, hlam, p11_1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h8, hlam, p11_0]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [h9, hlam, p11_1]
              · have p11_0 := h11c.1
                have p11_1 := h11c.2.1
                have p11_2 := h11c.2.2.1
                have p11_3 := h11c.2.2.2
                linarith only [hlam, p11_0]
            · linarith only [h10, h6, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
            · rcases h0bigk with h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h4, h8, hc01, hlam, hphi, ht0b, ht5b, p39_1, u5ehi0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h8, hc01, hlam, hphi, ht0b, ht5b, p39_1, u5ehi3]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                rcases p39_3 (m.d 0 1) (by simp) with h43 | h43
                · rcases p39_3 (m.d 0 2) (by simp) with h44 | h44
                  · linarith only [h0, h44, hlam]
                  · linarith only [h44, h5, hlam]
                · linarith only [h2, h43, hlam]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h3, h38, hc01, hlam, hphi, ht0b, ht5b, p39_1, u5ehi2]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h0, hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h8, hc02, hlam, hphi, ht0b, ht5b, p39_1, u5ehi3]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p39_1, u2elo0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h3, h38, hlam, hphi, ht01, ht0b, ht12, ht5b, p39_1, u2elo0, u5ehi2]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h1, hlam, p39_1]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h4, hlam, p39_1]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h2, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p39_1, u2elo0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h3, h38, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, p39_1, u2elo0, u5ehi2]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h2, hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h5, hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h7, hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h9, hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h3, hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h6, hlam, p39_1]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h8, hlam, p39_0]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [h2, h9, hc14, hc45, hlam, hphi, p39_1]
              · have p39_0 := h39c.1
                have p39_1 := h39c.2.1
                have p39_2 := h39c.2.2.1
                have p39_3 := h39c.2.2.2
                linarith only [hlam, p39_0]
            · linarith only [h38, h6, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h70 | h70
          · linarith only [h7, h70, h8, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h72 | h72
            · rcases h0bigk with h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [hlam, p73_0]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p73_1]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p73_1]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                rcases p73_3 (m.d 0 1) (by simp) with h77 | h77
                · rcases p73_3 (m.d 0 2) (by simp) with h78 | h78
                  · linarith only [h0, h78, hlam]
                  · linarith only [h5, h78, hlam]
                · linarith only [h2, h77, hlam]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p73_1]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h0, hlam, p73_0]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [hlam, p73_0]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h7, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p73_1]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p73_1, u2elo0]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h7, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p73_1, u2elo0]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h1, hlam, p73_1]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h4, hlam, p73_1]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [hlam, p73_0]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h2, h8, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p73_1]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h8, hlam, p73_1]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h2, hlam, p73_0]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h5, hlam, p73_0]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h7, hlam, p73_0]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [hlam, p73_0]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h70, hlam, p73_0]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h3, hlam, p73_0]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h6, hlam, p73_1]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h6, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p73_1, u2elo0]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [h2, h6, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p73_1, u2elo0]
              · have p73_0 := h73c.1
                have p73_1 := h73c.2.1
                have p73_2 := h73c.2.2.1
                have p73_3 := h73c.2.2.2
                linarith only [hlam, p73_0]
            · linarith only [h6, h72, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h104 | h104
        · rcases m.htr 0 4 5 (by decide) (by decide) with h105 | h105
          · rcases m.htr 1 2 5 (by decide) (by decide) with h106 | h106
            · rcases h0bigk with h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [hlam, p107_0]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p107_1]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h104, hc01, hlam, hphi, ht0b, ht5b, p107_1, u5ehi3]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h104, h7, hc01, hlam, hphi, ht0b, ht5b, p107_1, u5ehi3]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p107_1, u5ehi0]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h0, hlam, p107_0]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [hlam, p107_0]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h104, hc02, hlam, hphi, ht0b, ht5b, p107_1, u5ehi3]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h104, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, p107_1, u2elo0, u5ehi3]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h3, hlam, hphi, ht01, ht0b, ht12, ht5b, p107_1, u2elo0, u5ehi1]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h1, hlam, p107_1]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h4, hlam, p107_1]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [hlam, p107_0]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h7, hlam, p107_1]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h3, hc03, hlam, hphi, ht0b, ht5b, p107_1, u5ehi1]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h2, hlam, p107_0]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h5, hlam, p107_0]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p107_1, u2elo0]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [hlam, p107_0]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h3, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, p107_1, u2elo0, u5ehi1]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h3, hlam, p107_0]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h6, hlam, p107_1]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h104, hlam, p107_0]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [h105, hlam, p107_1]
              · have p107_0 := h107c.1
                have p107_1 := h107c.2.1
                have p107_2 := h107c.2.2.1
                have p107_3 := h107c.2.2.2
                linarith only [hlam, p107_0]
            · linarith only [h106, h6, hc12, hlam, hphi, u2elo0]
          · linarith only [h104, h105, h7, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h135 | h135
          · rcases m.htr 1 2 5 (by decide) (by decide) with h136 | h136
            · rcases h0bigk with h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [hlam, p137_0]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [h135, h5, hc01, hlam, hphi, ht0b, ht5b, p137_1, u5ehi4]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                rcases p137_3 (m.d 0 1) (by simp) with h140 | h140
                · rcases p137_3 (m.d 0 2) (by simp) with h141 | h141
                  · linarith only [h0, h141, hlam]
                  · linarith only [h141, h4, hlam]
                · linarith only [h1, h140, hlam]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [h135, hc01, hlam, hphi, ht0b, ht5b, p137_1, u5ehi4]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p137_1, u5ehi0]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [h0, hlam, p137_0]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [hlam, p137_0]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p137_1, u2elo0]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [h135, hlam, hphi, ht01, ht0b, ht12, ht5b, p137_1, u2elo0, u5ehi4]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [h136, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, p137_1, u2elo0, u5ehi2]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [h1, hlam, p137_1]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [h4, hlam, p137_1]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [hlam, p137_0]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [h7, hlam, p137_1]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [h104, hlam, p137_1]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [h2, hlam, p137_0]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [h5, hlam, p137_0]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [h1, h7, hc13, hc34, hlam, hphi, p137_1]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [hlam, p137_0]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [h136, h3, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, p137_1, u2elo0, u5ehi2]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [h3, hlam, p137_0]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [h6, hlam, p137_1]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [h1, h104, hc13, hc35, hlam, hphi, p137_1]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [h135, hlam, p137_1]
              · have p137_0 := h137c.1
                have p137_1 := h137c.2.1
                have p137_2 := h137c.2.2.1
                have p137_3 := h137c.2.2.2
                linarith only [hlam, p137_0]
            · linarith only [h136, h6, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h168 | h168
            · rcases h0bigk with h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [hlam, p169_0]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [h0, h168, hc01, hlam, hphi, ht0b, ht5b, p169_1, u5ehi2]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                rcases p169_3 (m.d 0 1) (by simp) with h172 | h172
                · rcases p169_3 (m.d 0 2) (by simp) with h173 | h173
                  · linarith only [h0, h173, hlam]
                  · linarith only [h173, h4, hlam]
                · linarith only [h1, h172, hlam]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                rcases p169_3 (m.d 0 1) (by simp) with h177 | h177
                · rcases p169_3 (m.d 0 2) (by simp) with h178 | h178
                  · linarith only [h0, h178, hlam]
                  · linarith only [h178, h5, hlam]
                · linarith only [h177, h2, hlam]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p169_1, u5ehi0]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [h0, hlam, p169_0]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [hlam, p169_0]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [h1, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p169_1, u2elo0]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p169_1, u2elo0]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [h3, hlam, hphi, ht01, ht0b, ht12, ht5b, p169_1, u2elo0, u5ehi1]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [h1, hlam, p169_1]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [h4, hlam, p169_1]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [hlam, p169_0]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [h7, hlam, p169_1]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [h104, hlam, p169_1]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [h2, hlam, p169_0]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [h5, hlam, p169_0]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [h1, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p169_1, u2elo0]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [hlam, p169_0]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [h135, hlam, p169_0]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [h3, hlam, p169_0]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [h6, hlam, p169_1]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [h1, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p169_1, u2elo0]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [h6, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p169_1, u2elo0]
              · have p169_0 := h169c.1
                have p169_1 := h169c.2.1
                have p169_2 := h169c.2.2.1
                have p169_3 := h169c.2.2.2
                linarith only [hlam, p169_0]
            · linarith only [h168, h6, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h204 | h204
      · rcases m.htr 0 3 5 (by decide) (by decide) with h205 | h205
        · linarith only [h205, h4, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h207 | h207
          · linarith only [h207, h5, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h209 | h209
            · linarith only [h209, h6, hc02, hlam, hphi, u2elo1]
            · rcases h0bigk with h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [hlam, p211_0]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p211_1]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [h204, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p211_1]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                rcases p211_3 (m.d 0 1) (by simp) with h215 | h215
                · rcases p211_3 (m.d 0 2) (by simp) with h216 | h216
                  · linarith only [h0, h216, hlam]
                  · linarith only [h216, h5, hlam]
                · linarith only [h2, h215, hlam]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p211_1, u5ehi0]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [h0, hlam, p211_0]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [hlam, p211_0]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [h204, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p211_1]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p211_1, u2elo0]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [h6, hlam, p211_0]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [h1, hlam, p211_1]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [h4, hlam, p211_1]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [hlam, p211_0]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [h2, h207, h4, h6, hc14, hc45, hlam, hphi, p211_1]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [h205, hlam, p211_1]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [h2, hlam, p211_0]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [h5, hlam, p211_0]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [h204, hlam, p211_0]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [hlam, p211_0]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [h207, hlam, p211_0]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [h3, hlam, p211_0]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [h205, hc02, hc35, hlam, hphi, ht23, p211_1]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [h6, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p211_1, u2elo4]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [h2, h6, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p211_1, u2elo4]
              · have p211_0 := h211c.1
                have p211_1 := h211c.2.1
                have p211_2 := h211c.2.2.1
                have p211_3 := h211c.2.2.2
                linarith only [hlam, p211_0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h241 | h241
        · linarith only [h204, h241, h5, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h243 | h243
          · linarith only [h243, h5, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h245 | h245
            · linarith only [h245, h6, hc02, hlam, hphi, u2elo1]
            · rcases h0bigk with h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [hlam, p247_0]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p247_1]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                rcases p247_3 (m.d 0 1) (by simp) with h250 | h250
                · rcases p247_3 (m.d 0 2) (by simp) with h251 | h251
                  · linarith only [h0, h251, hlam]
                  · linarith only [h251, h4, hlam]
                · linarith only [h1, h250, hlam]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                rcases p247_3 (m.d 0 1) (by simp) with h255 | h255
                · rcases p247_3 (m.d 0 2) (by simp) with h256 | h256
                  · linarith only [h0, h256, hlam]
                  · linarith only [h256, h5, hlam]
                · linarith only [h2, h255, hlam]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p247_1, u5ehi0]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [h0, hlam, p247_0]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [hlam, p247_0]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [h6, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p247_1, u2elo4]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [h6, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p247_1, u2elo4]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [h6, hlam, p247_0]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [h1, hlam, p247_1]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [h4, hlam, p247_1]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [hlam, p247_0]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [h204, hlam, p247_1]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [h241, hlam, p247_1]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [h2, hlam, p247_0]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [h5, hlam, p247_0]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [h1, h241, h5, h6, hc13, hc35, hlam, hphi, p247_1]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [hlam, p247_0]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [h243, hlam, p247_0]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [h3, hlam, p247_0]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [h241, hc02, hc35, hlam, hphi, ht23, p247_1]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [h1, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p247_1, u2elo4]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [h6, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p247_1, u2elo4]
              · have p247_0 := h247c.1
                have p247_1 := h247c.2.1
                have p247_2 := h247c.2.2.1
                have p247_3 := h247c.2.2.2
                linarith only [hlam, p247_0]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h281 | h281
    · linarith only [h281, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h283 | h283
      · linarith only [h283, h4, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h285 | h285
        · linarith only [h285, h4, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h287 | h287
          · rcases m.htr 1 2 5 (by decide) (by decide) with h288 | h288
            · linarith only [h281, h288, hc02, hlam, hphi, u2elo1]
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
                linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p290_1]
              · have p290_0 := h290c.1
                have p290_1 := h290c.2.1
                have p290_2 := h290c.2.2.1
                have p290_3 := h290c.2.2.2
                rcases p290_3 (m.d 0 1) (by simp) with h293 | h293
                · rcases p290_3 (m.d 0 2) (by simp) with h294 | h294
                  · linarith only [h0, h294, hlam]
                  · linarith only [h294, h4, hlam]
                · linarith only [h1, h293, hlam]
              · have p290_0 := h290c.1
                have p290_1 := h290c.2.1
                have p290_2 := h290c.2.2.1
                have p290_3 := h290c.2.2.2
                linarith only [h287, hc01, hlam, hphi, ht0b, ht5b, p290_1, u5ehi0]
              · have p290_0 := h290c.1
                have p290_1 := h290c.2.1
                have p290_2 := h290c.2.2.1
                have p290_3 := h290c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p290_1, u5ehi0]
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
                linarith only [h1, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p290_1, u2elo0]
              · have p290_0 := h290c.1
                have p290_1 := h290c.2.1
                have p290_2 := h290c.2.2.1
                have p290_3 := h290c.2.2.2
                linarith only [h5, hlam, p290_1]
              · have p290_0 := h290c.1
                have p290_1 := h290c.2.1
                have p290_2 := h290c.2.2.1
                have p290_3 := h290c.2.2.2
                linarith only [h281, hlam, p290_0]
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
                linarith only [h283, hlam, p290_1]
              · have p290_0 := h290c.1
                have p290_1 := h290c.2.1
                have p290_2 := h290c.2.2.1
                have p290_3 := h290c.2.2.2
                linarith only [h285, hlam, p290_1]
              · have p290_0 := h290c.1
                have p290_1 := h290c.2.1
                have p290_2 := h290c.2.2.1
                have p290_3 := h290c.2.2.2
                linarith only [h2, hlam, p290_0]
              · have p290_0 := h290c.1
                have p290_1 := h290c.2.1
                have p290_2 := h290c.2.2.1
                have p290_3 := h290c.2.2.2
                linarith only [h283, hc02, hc34, hlam, hphi, ht23, p290_1]
              · have p290_0 := h290c.1
                have p290_1 := h290c.2.1
                have p290_2 := h290c.2.2.1
                have p290_3 := h290c.2.2.2
                linarith only [h1, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p290_1, u2elo3]
              · have p290_0 := h290c.1
                have p290_1 := h290c.2.1
                have p290_2 := h290c.2.2.1
                have p290_3 := h290c.2.2.2
                linarith only [hlam, p290_0]
              · have p290_0 := h290c.1
                have p290_1 := h290c.2.1
                have p290_2 := h290c.2.2.1
                have p290_3 := h290c.2.2.2
                linarith only [h281, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p290_1, u2elo3]
              · have p290_0 := h290c.1
                have p290_1 := h290c.2.1
                have p290_2 := h290c.2.2.1
                have p290_3 := h290c.2.2.2
                linarith only [h3, hlam, p290_0]
              · have p290_0 := h290c.1
                have p290_1 := h290c.2.1
                have p290_2 := h290c.2.2.1
                have p290_3 := h290c.2.2.2
                linarith only [h4, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p290_1]
              · have p290_0 := h290c.1
                have p290_1 := h290c.2.1
                have p290_2 := h290c.2.2.1
                have p290_3 := h290c.2.2.2
                linarith only [h1, h281, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p290_1, u2elo4]
              · have p290_0 := h290c.1
                have p290_1 := h290c.2.1
                have p290_2 := h290c.2.2.1
                have p290_3 := h290c.2.2.2
                linarith only [h287, hlam, p290_1]
              · have p290_0 := h290c.1
                have p290_1 := h290c.2.1
                have p290_2 := h290c.2.2.1
                have p290_3 := h290c.2.2.2
                linarith only [hlam, p290_0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h320 | h320
            · linarith only [h0, h281, h320, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi0]
            · rcases h0bigk with h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [hlam, p322_0]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p322_1]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                rcases p322_3 (m.d 0 1) (by simp) with h325 | h325
                · rcases p322_3 (m.d 0 2) (by simp) with h326 | h326
                  · linarith only [h0, h326, hlam]
                  · linarith only [h326, h4, hlam]
                · linarith only [h1, h325, hlam]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h4, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p322_1]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h287, h4, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p322_1]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h0, hlam, p322_0]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [hlam, p322_0]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h1, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p322_1, u2elo3]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h5, hlam, p322_1]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h281, hlam, p322_0]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h1, hlam, p322_1]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h4, hlam, p322_1]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [hlam, p322_0]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h283, hlam, p322_1]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h285, hlam, p322_1]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h2, hlam, p322_0]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h287, h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p322_1]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h1, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p322_1, u2elo3]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [hlam, p322_0]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h287, hlam, p322_0]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h3, hlam, p322_0]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h281, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p322_1, u2elo4]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h1, h281, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p322_1, u2elo4]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [h281, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p322_1, u2elo4]
              · have p322_0 := h322c.1
                have p322_1 := h322c.2.1
                have p322_2 := h322c.2.2.1
                have p322_3 := h322c.2.2.2
                linarith only [hlam, p322_0]

end R2N4
