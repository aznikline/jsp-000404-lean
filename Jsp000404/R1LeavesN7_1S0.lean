import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
  · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
    · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
      · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
        · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
          · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
            · linarith only [h0, h10, h16, h19, hc01, hc45, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10, h16, h18, h19, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
            · linarith only [h0, h10, h13, h18, h22, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases h0bigk with h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h0, h10, h17, hc01, hc35, hlam, hphi, ht0b, ht5b, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h16, h18, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h16, h18, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                rcases p24_3 (m.d 0 1) (by simp) with h29 | h29
                · rcases p24_3 (m.d 0 2) (by simp) with h30 | h30
                  · linarith only [h0, h30, hlam]
                  · linarith only [h30, h6, hlam]
                · linarith only [h29, h3, hlam]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h0, hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h1, h13, h15, h16, h18, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h0, h15, h16, h18, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                rcases p24_3 (m.d 0 1) (by simp) with h38 | h38
                · rcases p24_3 (m.d 0 2) (by simp) with h39 | h39
                  · rcases p24_3 (m.d 0 3) (by simp) with h40 | h40
                    · linarith only [h4, h40, hlam]
                    · linarith only [h40, h8, hlam]
                  · linarith only [h39, h6, hlam]
                · linarith only [h3, h38, hlam]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h1, hlam, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h4, hlam, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h15, h16, h18, h2, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                rcases p24_3 (m.d 0 1) (by simp) with h49 | h49
                · rcases p24_3 (m.d 0 2) (by simp) with h50 | h50
                  · rcases p24_3 (m.d 0 3) (by simp) with h51 | h51
                    · rcases p24_3 (m.d 0 4) (by simp) with h52 | h52
                      · linarith only [h52, h7, hlam]
                      · linarith only [h52, h9, hlam]
                    · linarith only [h51, h8, hlam]
                  · linarith only [h50, h6, hlam]
                · linarith only [h3, h49, hlam]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h2, hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h5, hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h7, hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                rcases p24_3 (m.d 0 1) (by simp) with h62 | h62
                · rcases p24_3 (m.d 0 2) (by simp) with h63 | h63
                  · rcases p24_3 (m.d 0 3) (by simp) with h64 | h64
                    · rcases p24_3 (m.d 0 4) (by simp) with h65 | h65
                      · rcases p24_3 (m.d 0 5) (by simp) with h66 | h66
                        · linarith only [h66, h9, hlam]
                        · rcases h2bigk with h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h10, h13, h15, h16, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            rcases p68_3 (m.d 0 2) (by simp) with h71 | h71
                            · rcases p68_3 (m.d 1 2) (by simp) with h72 | h72
                              · linarith only [h0, h72, hlam]
                              · linarith only [h10, h72, hlam]
                            · linarith only [h71, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h18, h4, h7, h9, hlam, p24_1, p68_2]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            rcases p68_3 (m.d 0 2) (by simp) with h77 | h77
                            · rcases p68_3 (m.d 1 2) (by simp) with h78 | h78
                              · linarith only [h0, h78, hlam]
                              · linarith only [h12, h78, hlam]
                            · linarith only [h77, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h16, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            rcases p68_3 (m.d 0 2) (by simp) with h85 | h85
                            · rcases p68_3 (m.d 1 2) (by simp) with h86 | h86
                              · rcases p68_3 (m.d 2 3) (by simp) with h87 | h87
                                · linarith only [h10, h87, hlam]
                                · linarith only [h16, h87, hlam]
                              · linarith only [h86, hlam, p68_0]
                            · linarith only [h5, h85, hlam]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            rcases p68_3 (m.d 0 2) (by simp) with h92 | h92
                            · rcases p68_3 (m.d 1 2) (by simp) with h93 | h93
                              · rcases p68_3 (m.d 2 3) (by simp) with h94 | h94
                                · linarith only [h10, h94, hlam]
                                · linarith only [h17, h94, hlam]
                              · linarith only [h93, hlam, p68_0]
                            · linarith only [h6, h92, hlam]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h4, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h10, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h10, h16, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h10, hc01, hc25, hlam, hphi, ht0b, ht5b, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h5, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h11, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h16, hlam, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h18, hlam, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h6, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h12, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h17, hlam, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h16, h4, h6, h7, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                      · linarith only [h65, h9, hlam]
                    · linarith only [h64, h8, hlam]
                  · linarith only [h6, h63, hlam]
                · linarith only [h3, h62, hlam]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h3, hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h6, hlam, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h8, hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h9, hlam, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [hlam, p24_0]
        · linarith only [h0, h10, h14, h16, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h124 | h124
        · linarith only [h0, h10, h124, h13, h16, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h126 | h126
          · rcases m.htr 3 4 5 (by decide) (by decide) with h127 | h127
            · rcases h0bigk with h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hlam, p128_0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [h0, h10, h124, h127, h13, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p128_1]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [h1, h124, h127, h13, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p128_1]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                rcases p128_3 (m.d 0 1) (by simp) with h132 | h132
                · rcases p128_3 (m.d 0 2) (by simp) with h133 | h133
                  · linarith only [h0, h133, hlam]
                  · linarith only [h133, h5, hlam]
                · linarith only [h132, h2, hlam]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                rcases p128_3 (m.d 0 1) (by simp) with h137 | h137
                · rcases p128_3 (m.d 0 2) (by simp) with h138 | h138
                  · linarith only [h0, h138, hlam]
                  · linarith only [h138, h6, hlam]
                · linarith only [h137, h3, hlam]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [h0, hlam, p128_0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hlam, p128_0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [h1, h124, h127, h13, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p128_1]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                rcases p128_3 (m.d 0 1) (by simp) with h145 | h145
                · rcases p128_3 (m.d 0 2) (by simp) with h146 | h146
                  · rcases p128_3 (m.d 0 3) (by simp) with h147 | h147
                    · linarith only [h147, h4, hlam]
                    · linarith only [h147, h7, hlam]
                  · linarith only [h146, h5, hlam]
                · linarith only [h145, h2, hlam]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                rcases p128_3 (m.d 0 1) (by simp) with h152 | h152
                · rcases p128_3 (m.d 0 2) (by simp) with h153 | h153
                  · rcases p128_3 (m.d 0 3) (by simp) with h154 | h154
                    · linarith only [h154, h4, hlam]
                    · linarith only [h154, h8, hlam]
                  · linarith only [h153, h6, hlam]
                · linarith only [h152, h3, hlam]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [h1, hlam, p128_1]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [h4, hlam, p128_1]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hlam, p128_0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                rcases p128_3 (m.d 0 1) (by simp) with h162 | h162
                · rcases p128_3 (m.d 0 2) (by simp) with h163 | h163
                  · rcases p128_3 (m.d 0 3) (by simp) with h164 | h164
                    · rcases p128_3 (m.d 0 4) (by simp) with h165 | h165
                      · linarith only [h165, h7, hlam]
                      · rcases p128_3 (m.d 0 5) (by simp) with h167 | h167
                        · linarith only [h167, h8, hlam]
                        · rcases h2bigk with h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [hlam, p169_0]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [h0, h10, h124, h127, h13, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p169_1]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [h124, h14, h15, h2, h4, hlam, p128_1, p169_2]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            rcases p169_3 (m.d 0 2) (by simp) with h173 | h173
                            · rcases p169_3 (m.d 1 2) (by simp) with h174 | h174
                              · linarith only [h0, h174, hlam]
                              · linarith only [h11, h174, hlam]
                            · linarith only [h173, hlam, p169_0]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            rcases p169_3 (m.d 0 2) (by simp) with h178 | h178
                            · rcases p169_3 (m.d 1 2) (by simp) with h179 | h179
                              · linarith only [h0, h179, hlam]
                              · linarith only [h12, h179, hlam]
                            · linarith only [h178, hlam, p169_0]
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
                            rcases p169_3 (m.d 0 2) (by simp) with h185 | h185
                            · rcases p169_3 (m.d 1 2) (by simp) with h186 | h186
                              · rcases p169_3 (m.d 2 3) (by simp) with h187 | h187
                                · linarith only [h187, hlam, p169_0]
                                · rcases p169_3 (m.d 2 4) (by simp) with h189 | h189
                                  · linarith only [h11, h189, hlam]
                                  · linarith only [h16, h189, hlam]
                              · linarith only [h186, hlam, p169_0]
                            · linarith only [h185, h4, hlam]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [h0, h126, hc01, hc45, hlam, hphi, ht0b, ht5b, p169_1]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            rcases p169_3 (m.d 0 2) (by simp) with h195 | h195
                            · rcases p169_3 (m.d 1 2) (by simp) with h196 | h196
                              · rcases p169_3 (m.d 2 3) (by simp) with h197 | h197
                                · linarith only [h10, h197, hlam]
                                · rcases p169_3 (m.d 2 4) (by simp) with h199 | h199
                                  · linarith only [h11, h199, hlam]
                                  · linarith only [h126, h199, hlam]
                              · linarith only [h196, hlam, p169_0]
                            · linarith only [h195, h6, hlam]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [h4, hlam, p169_0]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [h10, hlam, p169_0]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [hlam, p169_0]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [h16, hlam, p169_0]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [h124, hlam, p169_0]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [h5, hlam, p169_0]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [h11, hlam, p169_0]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [h4, h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p128_1, p169_1]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [hlam, p169_0]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [h1, h13, h16, hc01, hc25, hlam, hphi, ht0b, ht5b, p169_1]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [h6, hlam, p169_0]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [h12, hlam, p169_0]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [h0, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p128_1, p169_1]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [h126, hlam, p169_0]
                          · have p169_0 := h169c.1
                            have p169_1 := h169c.2.1
                            have p169_2 := h169c.2.2.1
                            have p169_3 := h169c.2.2.2
                            linarith only [hlam, p169_0]
                    · linarith only [h164, h7, hlam]
                  · linarith only [h163, h5, hlam]
                · linarith only [h162, h2, hlam]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                rcases p128_3 (m.d 0 1) (by simp) with h222 | h222
                · rcases p128_3 (m.d 0 2) (by simp) with h223 | h223
                  · rcases p128_3 (m.d 0 3) (by simp) with h224 | h224
                    · rcases p128_3 (m.d 0 4) (by simp) with h225 | h225
                      · linarith only [h225, h7, hlam]
                      · linarith only [h225, h9, hlam]
                    · linarith only [h224, h8, hlam]
                  · linarith only [h223, h6, hlam]
                · linarith only [h222, h3, hlam]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [h2, hlam, p128_0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [h5, hlam, p128_0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [h7, hlam, p128_0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hlam, p128_0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                rcases p128_3 (m.d 0 1) (by simp) with h235 | h235
                · rcases p128_3 (m.d 0 2) (by simp) with h236 | h236
                  · rcases p128_3 (m.d 0 3) (by simp) with h237 | h237
                    · rcases p128_3 (m.d 0 4) (by simp) with h238 | h238
                      · rcases p128_3 (m.d 0 5) (by simp) with h239 | h239
                        · linarith only [h239, h9, hlam]
                        · rcases h2bigk with h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h0, h10, h124, h14, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p241_1]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h124, h14, h3, h5, hlam, p128_1, p241_2]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            rcases p241_3 (m.d 0 2) (by simp) with h245 | h245
                            · rcases p241_3 (m.d 1 2) (by simp) with h246 | h246
                              · linarith only [h0, h246, hlam]
                              · linarith only [h11, h246, hlam]
                            · linarith only [h245, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            rcases p241_3 (m.d 0 2) (by simp) with h250 | h250
                            · rcases p241_3 (m.d 1 2) (by simp) with h251 | h251
                              · linarith only [h0, h251, hlam]
                              · linarith only [h12, h251, hlam]
                            · linarith only [h250, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h0, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            rcases p241_3 (m.d 0 2) (by simp) with h257 | h257
                            · rcases p241_3 (m.d 1 2) (by simp) with h258 | h258
                              · rcases p241_3 (m.d 2 3) (by simp) with h259 | h259
                                · linarith only [h259, hlam, p241_0]
                                · rcases p241_3 (m.d 2 4) (by simp) with h261 | h261
                                  · linarith only [h11, h261, hlam]
                                  · linarith only [h16, h261, hlam]
                              · linarith only [h258, hlam, p241_0]
                            · linarith only [h257, h4, hlam]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h0, h126, hc01, hc45, hlam, hphi, ht0b, ht5b, p241_1]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            rcases p241_3 (m.d 0 2) (by simp) with h267 | h267
                            · rcases p241_3 (m.d 1 2) (by simp) with h268 | h268
                              · rcases p241_3 (m.d 2 3) (by simp) with h269 | h269
                                · linarith only [h10, h269, hlam]
                                · rcases p241_3 (m.d 2 4) (by simp) with h271 | h271
                                  · linarith only [h11, h271, hlam]
                                  · linarith only [h126, h271, hlam]
                              · linarith only [h268, hlam, p241_0]
                            · linarith only [h267, h6, hlam]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h4, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h10, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h16, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h124, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h5, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h11, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p241_1]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h1, h13, h16, hc01, hc25, hlam, hphi, ht0b, ht5b, p241_1]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h6, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h12, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h4, h6, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p128_1, p241_1]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h126, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hlam, p241_0]
                      · linarith only [h238, h9, hlam]
                    · linarith only [h237, h8, hlam]
                  · linarith only [h236, h6, hlam]
                · linarith only [h235, h3, hlam]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [h3, hlam, p128_0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [h6, hlam, p128_1]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [h8, hlam, p128_0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [h9, hlam, p128_1]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hlam, p128_0]
            · linarith only [h0, h10, h127, h13, h15, h16, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h301 | h301
            · linarith only [h0, h10, h126, h13, h301, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h13, h15, h16, h301, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h304 | h304
      · rcases m.htr 2 3 5 (by decide) (by decide) with h305 | h305
        · rcases m.htr 2 4 5 (by decide) (by decide) with h306 | h306
          · linarith only [h0, h11, h15, h306, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h308 | h308
            · linarith only [h11, h15, h304, h308, hlam]
            · rcases h0bigk with h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h11, h15, h304, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p310_1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h11, h15, h304, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p310_1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h11, h15, h304, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p310_1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                rcases p310_3 (m.d 0 1) (by simp) with h315 | h315
                · rcases p310_3 (m.d 0 2) (by simp) with h316 | h316
                  · linarith only [h0, h316, hlam]
                  · linarith only [h316, h6, hlam]
                · linarith only [h3, h315, hlam]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h0, hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h11, h15, h304, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p310_1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h0, h11, h15, h304, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p310_1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                rcases p310_3 (m.d 0 1) (by simp) with h324 | h324
                · rcases p310_3 (m.d 0 2) (by simp) with h325 | h325
                  · rcases p310_3 (m.d 0 3) (by simp) with h326 | h326
                    · linarith only [h326, h4, hlam]
                    · linarith only [h326, h8, hlam]
                  · linarith only [h325, h6, hlam]
                · linarith only [h3, h324, hlam]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h1, hlam, p310_1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h4, hlam, p310_1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h11, h15, h304, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p310_1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                rcases p310_3 (m.d 0 1) (by simp) with h335 | h335
                · rcases p310_3 (m.d 0 2) (by simp) with h336 | h336
                  · rcases p310_3 (m.d 0 3) (by simp) with h337 | h337
                    · rcases p310_3 (m.d 0 4) (by simp) with h338 | h338
                      · linarith only [h338, h7, hlam]
                      · linarith only [h338, h9, hlam]
                    · linarith only [h337, h8, hlam]
                  · linarith only [h336, h6, hlam]
                · linarith only [h3, h335, hlam]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h2, hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h5, hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h7, hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                rcases p310_3 (m.d 0 1) (by simp) with h348 | h348
                · rcases p310_3 (m.d 0 2) (by simp) with h349 | h349
                  · rcases p310_3 (m.d 0 3) (by simp) with h350 | h350
                    · rcases p310_3 (m.d 0 4) (by simp) with h351 | h351
                      · rcases p310_3 (m.d 0 5) (by simp) with h352 | h352
                        · linarith only [h352, h9, hlam]
                        · rcases h2bigk with h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [hlam, p354_0]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [h0, h10, h304, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p354_1]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            rcases p354_3 (m.d 0 2) (by simp) with h357 | h357
                            · rcases p354_3 (m.d 1 2) (by simp) with h358 | h358
                              · linarith only [h0, h358, hlam]
                              · linarith only [h10, h358, hlam]
                            · linarith only [h357, hlam, p354_0]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [h11, h15, h5, h9, hlam, p310_1, p354_2]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            rcases p354_3 (m.d 0 2) (by simp) with h363 | h363
                            · rcases p354_3 (m.d 1 2) (by simp) with h364 | h364
                              · linarith only [h0, h364, hlam]
                              · linarith only [h12, h364, hlam]
                            · linarith only [h363, hlam, p354_0]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [h0, hlam, p354_0]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [hlam, p354_0]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [h0, h305, h308, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p354_1]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            rcases p354_3 (m.d 0 2) (by simp) with h371 | h371
                            · rcases p354_3 (m.d 1 2) (by simp) with h372 | h372
                              · rcases p354_3 (m.d 2 3) (by simp) with h373 | h373
                                · linarith only [h10, h373, hlam]
                                · linarith only [h304, h373, hlam]
                              · linarith only [h372, hlam, p354_0]
                            · linarith only [h371, h5, hlam]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            rcases p354_3 (m.d 0 2) (by simp) with h378 | h378
                            · rcases p354_3 (m.d 1 2) (by simp) with h379 | h379
                              · rcases p354_3 (m.d 2 3) (by simp) with h380 | h380
                                · linarith only [h10, h380, hlam]
                                · linarith only [h305, h380, hlam]
                              · linarith only [h379, hlam, p354_0]
                            · linarith only [h378, h6, hlam]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [h4, hlam, p354_0]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [h10, hlam, p354_0]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [hlam, p354_0]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [h0, h10, h304, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p354_1]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [h0, h10, hc01, hc25, hlam, hphi, ht0b, ht5b, p354_1]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [h5, hlam, p354_0]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [h11, hlam, p354_0]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [h304, hlam, p354_1]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [hlam, p354_0]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [h306, hlam, p354_1]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [h6, hlam, p354_0]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [h12, hlam, p354_0]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [h305, hlam, p354_1]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [h304, h4, h6, h7, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p310_1, p354_1]
                          · have p354_0 := h354c.1
                            have p354_1 := h354c.2.1
                            have p354_2 := h354c.2.2.1
                            have p354_3 := h354c.2.2.2
                            linarith only [hlam, p354_0]
                      · linarith only [h351, h9, hlam]
                    · linarith only [h350, h8, hlam]
                  · linarith only [h349, h6, hlam]
                · linarith only [h3, h348, hlam]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h3, hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h6, hlam, p310_1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h8, hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h9, hlam, p310_1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hlam, p310_0]
        · linarith only [h0, h10, h14, h304, h305, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h410 | h410
        · linarith only [h0, h10, h13, h304, h410, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h412 | h412
          · linarith only [h13, h15, h304, h412, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h414 | h414
            · linarith only [h13, h15, h414, hlam]
            · rcases h0bigk with h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [hlam, p416_0]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h13, h15, h304, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p416_1]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h13, h15, h304, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p416_1]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h13, h15, h304, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p416_1]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h13, h15, h304, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p416_1]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h0, hlam, p416_0]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [hlam, p416_0]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h13, h15, h304, h7, h9, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p416_1]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h0, h13, h15, h304, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p416_1]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h0, h13, h15, h304, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p416_1]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h1, hlam, p416_1]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h4, hlam, p416_1]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [hlam, p416_0]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h13, h15, h304, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p416_1]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h0, h13, h15, h304, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p416_1]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h2, hlam, p416_0]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h5, hlam, p416_0]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h7, hlam, p416_0]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [hlam, p416_0]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h13, h15, h304, h9, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p416_1]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h3, hlam, p416_0]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h6, hlam, p416_1]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h8, hlam, p416_0]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [h9, hlam, p416_1]
              · have p416_0 := h416c.1
                have p416_1 := h416c.2.1
                have p416_2 := h416c.2.2.1
                have p416_3 := h416c.2.2.2
                linarith only [hlam, p416_0]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h442 | h442
    · linarith only [h13, h14, h442, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h444 | h444
      · rcases m.htr 2 3 5 (by decide) (by decide) with h445 | h445
        · linarith only [h10, h14, h445, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h447 | h447
          · linarith only [h0, h11, h442, h447, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h449 | h449
            · linarith only [h13, h14, h442, h449, hlam]
            · rcases h0bigk with h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h10, h14, h4, h444, h449, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h10, h14, h444, h449, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h10, h14, h444, h449, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h10, h14, h444, h449, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h0, hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h10, h14, h444, h449, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h0, h10, h14, h444, h449, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h0, h10, h14, h444, h449, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h1, hlam, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h4, hlam, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h10, h14, h444, h449, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h0, h10, h14, h4, h444, h449, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h2, hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h5, hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h7, hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h10, h14, h444, h449, h9, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h3, hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h6, hlam, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h8, hlam, p451_0]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [h9, hlam, p451_1]
              · have p451_0 := h451c.1
                have p451_1 := h451c.2.1
                have p451_2 := h451c.2.2.1
                have p451_3 := h451c.2.2.2
                linarith only [hlam, p451_0]
      · linarith only [h13, h14, h444, hc23, hc35, hlam, hphi]

end R2N4
