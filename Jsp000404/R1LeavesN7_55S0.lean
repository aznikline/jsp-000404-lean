import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4318000 in
theorem r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                  · linarith only [h0, h13, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h10, h13, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                  · linarith only [h0, h16, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h10, h16, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h1, h10, h11, h5, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
              · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
                · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                  · linarith only [h10, h20, h22, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                    · linarith only [h0, h24, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h10, h20, h24, hc23, hc34, hlam, hphi]
                · linarith only [h10, h2, h20, h21, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28 | h28
                · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                  · linarith only [h0, h10, h29, h7, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31 | h31
                    · linarith only [h0, h31, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                      · linarith only [h0, h33, h8, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h2, h28, h33, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                  · linarith only [h10, h36, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h38 | h38
                    · linarith only [h10, h2, h28, h38, h6, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h40 | h40
                      · linarith only [h0, h10, h28, h40, h7, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h42 | h42
                        · rcases h5bigk with h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [hlam, p43_0]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h10, h28, h4, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p43_1, u2elo0]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p43_1, u2elo0]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h10, h28, h4, h42, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p43_1, u2elo0]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h10, h28, h4, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p43_1, u2elo0]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h3, hlam, p43_0]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [hlam, p43_0]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p43_1, u1elo4]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h20, hlam, p43_0]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h28, hlam, p43_0]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h4, hlam, p43_1]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h9, hlam, p43_1]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [hlam, p43_0]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h38, hlam, p43_1]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h40, hlam, p43_0]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h5, hlam, p43_1]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h1, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p43_1, u1elo0]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h1, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, p43_1, u1elo0]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [hlam, p43_0]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h1, h10, h28, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p43_1, u1elo0]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h6, hlam, p43_1]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h10, h28, h42, h7, hc23, hc34, hlam, hphi, p43_1]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h2, h36, h40, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p43_1, u1elo0]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [h42, hlam, p43_1]
                          · have p43_0 := h43c.1
                            have p43_1 := h43c.2.1
                            have p43_2 := h43c.2.2.1
                            have p43_3 := h43c.2.2.2
                            linarith only [hlam, p43_0]
                        · linarith only [h10, h2, h42, h6, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · linarith only [h4, h9, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
          · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
            · linarith only [h7, h72, h8, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
              · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                  · linarith only [h7, h72, h76, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h78 | h78
                    · linarith only [h7, h78, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h1, h74, h78, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · linarith only [h2, h6, h7, h75, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                  · linarith only [h7, h72, h83, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h85 | h85
                    · linarith only [h7, h8, h85, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h88 | h88
                        · rcases h5bigk with h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [hlam, p89_0]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p89_1, u2elo0]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h4, h87, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p89_1, u2elo0]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h4, h74, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p89_1, u2elo0]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p89_1, u2elo0]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h3, hlam, p89_0]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [hlam, p89_0]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h87, hc45, hlam, hphi, ht01, ht0b, ht5b, p89_1, u1elo4]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h74, hlam, p89_0]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h71, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p89_1, u2elo3]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h4, hlam, p89_1]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h71, hlam, p89_1]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [hlam, p89_0]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h85, hlam, p89_1]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p89_1, u2elo4]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h5, hlam, p89_1]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h1, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p89_1, u1elo0]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h1, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, p89_1, u1elo0]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [hlam, p89_0]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h1, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p89_1, u1elo0]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h6, hlam, p89_1]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h82, hlam, p89_1]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h87, hlam, p89_1]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [h88, hlam, p89_1]
                          · have p89_0 := h89c.1
                            have p89_1 := h89c.2.1
                            have p89_2 := h89c.2.2.1
                            have p89_3 := h89c.2.2.2
                            linarith only [hlam, p89_0]
                        · linarith only [h2, h6, h8, h83, h88, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h71, h8, h82, h85, h87, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                · linarith only [h2, h6, h71, h8, h82, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
          · linarith only [h4, h7, h71, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h119 | h119
        · rcases m.htr 1 2 5 (by decide) (by decide) with h120 | h120
          · rcases m.htr 1 3 4 (by decide) (by decide) with h121 | h121
            · rcases m.htr 1 3 5 (by decide) (by decide) with h122 | h122
              · rcases m.htr 1 4 5 (by decide) (by decide) with h123 | h123
                · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h125 | h125
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h126 | h126
                      · linarith only [h119, h126, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                      · linarith only [h119, h123, h126, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                    · linarith only [h1, h125, h5, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1, h121, h124, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h131 | h131
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h132 | h132
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h133 | h133
                      · linarith only [h119, h123, h133, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h135 | h135
                        · linarith only [h119, h123, h131, h135, hlam]
                        · rcases h5bigk with h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h3, hc15, hlam, hphi, ht01, ht0b, ht5b, p137_1, u1elo0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p137_1, u2elo0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p137_1, u2elo0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h119, h123, h131, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p137_1, u2elo0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h3, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h132, hc35, hlam, hphi, ht01, ht0b, ht5b, p137_1, u1elo4]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h120, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p137_1, u2elo2]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h123, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h4, hlam, p137_1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h120, hlam, p137_1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p137_1, u2elo4]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h133, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h5, hlam, p137_1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h122, hlam, p137_1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h132, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h135, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h6, hlam, p137_1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h2, h6, hc15, hlam, hphi, ht01, ht0b, ht5b, p137_1, u1elo0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h2, h6, hc25, hlam, hphi, ht01, ht0b, ht5b, p137_1, u1elo0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h2, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, p137_1, u1elo0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [hlam, p137_0]
                    · linarith only [h1, h132, h5, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1, h119, h121, h131, h7, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h1, h121, h122, h5, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h119, h121, h7, hlam]
          · linarith only [h119, h120, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h168 | h168
          · rcases m.htr 1 3 4 (by decide) (by decide) with h169 | h169
            · rcases m.htr 1 3 5 (by decide) (by decide) with h170 | h170
              · rcases m.htr 1 4 5 (by decide) (by decide) with h171 | h171
                · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h173 | h173
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h174 | h174
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h175 | h175
                        · linarith only [h1, h169, h175, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h171, h175, h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h1, h119, h169, h171, h174, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h1, h119, h168, h172, h173, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h1, h168, h169, h172, h7, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · linarith only [h119, h168, h171, h2, h6, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h1, h169, h170, h5, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h183 | h183
              · rcases m.htr 1 4 5 (by decide) (by decide) with h184 | h184
                · rcases m.htr 2 3 4 (by decide) (by decide) with h185 | h185
                  · linarith only [h168, h169, h185, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h187 | h187
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h188 | h188
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h189 | h189
                        · rcases h5bigk with h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [hlam, p190_0]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h168, h187, h189, h3, hc45, hlam, hphi, ht01, ht0b, ht5b, p190_1, u1elo0]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h187, h189, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p190_1, u2elo0]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h189, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p190_1, u2elo0]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p190_1, u2elo0]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h3, hlam, p190_0]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [hlam, p190_0]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h187, h189, hc45, hlam, hphi, ht01, ht0b, ht5b, p190_1, u1elo4]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h168, h189, hc45, hlam, hphi, ht01, ht0b, ht5b, p190_1, u1elo1]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h168, h185, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p190_1, u2elo3]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h4, hlam, p190_1]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h168, hlam, p190_1]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [hlam, p190_0]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h189, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p190_1, u2elo4]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h168, h185, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p190_1, u2elo3]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h5, hlam, p190_1]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h183, hlam, p190_1]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h187, hlam, p190_0]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [hlam, p190_0]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h1, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p190_1, u1elo0]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h6, hlam, p190_1]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h184, hlam, p190_1]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h188, hlam, p190_1]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [h189, hlam, p190_1]
                          · have p190_0 := h190c.1
                            have p190_1 := h190c.2.1
                            have p190_2 := h190c.2.2.1
                            have p190_3 := h190c.2.2.2
                            linarith only [hlam, p190_0]
                        · linarith only [h169, h189, h2, h6, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h184, h185, h188, h2, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h1, h168, h187, h5, h7, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · linarith only [h119, h168, h184, h2, h6, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h1, h168, h183, h5, h7, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
          · linarith only [h168, h4, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
      · rcases m.htr 1 2 4 (by decide) (by decide) with h223 | h223
        · rcases m.htr 1 2 5 (by decide) (by decide) with h224 | h224
          · rcases m.htr 1 3 4 (by decide) (by decide) with h225 | h225
            · rcases m.htr 1 3 5 (by decide) (by decide) with h226 | h226
              · rcases m.htr 1 4 5 (by decide) (by decide) with h227 | h227
                · linarith only [h2, h227, h6, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h229 | h229
                  · linarith only [h0, h222, h229, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1, h225, h229, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h1, h225, h226, h5, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h233 | h233
              · rcases m.htr 1 4 5 (by decide) (by decide) with h234 | h234
                · linarith only [h2, h234, h6, hlam]
                · linarith only [h225, h233, h234, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h237 | h237
                · linarith only [h2, h237, h6, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                  · linarith only [h222, h225, h239, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h241 | h241
                    · linarith only [h222, h233, h241, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h243 | h243
                      · linarith only [h0, h223, h243, h6, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h245 | h245
                        · linarith only [h245, h5, h6, hlam]
                        · rcases h5bigk with h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [hlam, p247_0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h3, hc15, hlam, hphi, ht01, ht0b, ht5b, p247_1, u1elo0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p247_1, u2elo0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p247_1, u2elo0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h6, hlam, p247_0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h3, hlam, p247_0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [hlam, p247_0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p247_1, u1elo4]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h233, hlam, p247_0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h237, hlam, p247_0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h4, hlam, p247_1]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h224, hlam, p247_1]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [hlam, p247_0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h241, hlam, p247_1]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h243, hlam, p247_0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h5, hlam, p247_1]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h1, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p247_1, u1elo0]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h1, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, p247_1, u1elo0]
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
                            linarith only [h222, h225, h237, h3, hc23, hc45, hlam, hphi, ht34, p247_1]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h222, h225, h237, hc23, hc45, hlam, hphi, ht34, p247_1]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h241, hc23, hc45, hlam, hphi, ht34, p247_1]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [h222, h233, hc23, hc45, hlam, hphi, ht34, p247_1]
                          · have p247_0 := h247c.1
                            have p247_1 := h247c.2.1
                            have p247_2 := h247c.2.2.1
                            have p247_3 := h247c.2.2.2
                            linarith only [hlam, p247_0]
          · linarith only [h224, h4, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h274 | h274
          · rcases m.htr 1 3 4 (by decide) (by decide) with h275 | h275
            · linarith only [h222, h223, h275, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h277 | h277
              · rcases m.htr 1 4 5 (by decide) (by decide) with h278 | h278
                · linarith only [h2, h278, h6, hlam]
                · linarith only [h223, h274, h278, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h281 | h281
                · linarith only [h2, h281, h6, hlam]
                · linarith only [h223, h274, h281, hlam]
          · linarith only [h222, h274, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h285 | h285
        · rcases m.htr 1 2 5 (by decide) (by decide) with h286 | h286
          · rcases m.htr 1 3 4 (by decide) (by decide) with h287 | h287
            · rcases m.htr 1 3 5 (by decide) (by decide) with h288 | h288
              · rcases m.htr 1 4 5 (by decide) (by decide) with h289 | h289
                · linarith only [h2, h289, h6, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h291 | h291
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h292 | h292
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h293 | h293
                      · linarith only [h2, h285, h293, h6, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h295 | h295
                        · linarith only [h2, h285, h291, h295, h6, hlam]
                        · rcases h5bigk with h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h286, h292, h3, hc35, hlam, hphi, ht01, ht0b, ht5b, p297_1, u1elo0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h0, h292, h4, hc35, hlam, hphi, ht01, ht0b, ht5b, p297_1, u1elo0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h0, h4, hc35, hlam, hphi, ht01, ht0b, ht5b, p297_1, u1elo0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h6, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h3, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h292, hc35, hlam, hphi, ht01, ht0b, ht5b, p297_1, u1elo4]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h222, h286, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p297_1, u2elo2]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h289, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h4, hlam, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h286, hlam, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p297_1, u2elo4]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h293, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h5, hlam, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h288, hlam, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h292, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h295, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h6, hc04, hc45, hlam, hphi, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h285, h289, h291, hc34, hc45, hlam, hphi, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h291, h293, hc34, hc45, hlam, hphi, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h295, hc34, hc45, hlam, hphi, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [hlam, p297_0]
                    · linarith only [h1, h222, h292, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1, h222, h287, h291, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h1, h222, h285, h288, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h222, h285, h287, hlam]
          · linarith only [h285, h286, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h328 | h328
          · rcases m.htr 1 3 4 (by decide) (by decide) with h329 | h329
            · rcases m.htr 1 3 5 (by decide) (by decide) with h330 | h330
              · rcases m.htr 1 4 5 (by decide) (by decide) with h331 | h331
                · linarith only [h2, h331, h6, hlam]
                · linarith only [h285, h328, h331, hlam]
              · linarith only [h1, h329, h330, h5, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h335 | h335
              · rcases m.htr 1 4 5 (by decide) (by decide) with h336 | h336
                · linarith only [h2, h336, h6, hlam]
                · linarith only [h222, h328, h329, h336, hlam]
              · linarith only [h1, h222, h328, h335, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
          · linarith only [h328, h4, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h341 | h341
    · rcases m.htr 1 2 3 (by decide) (by decide) with h342 | h342
      · rcases m.htr 1 2 4 (by decide) (by decide) with h343 | h343
        · rcases m.htr 1 2 5 (by decide) (by decide) with h344 | h344
          · rcases m.htr 1 3 4 (by decide) (by decide) with h345 | h345
            · rcases m.htr 1 3 5 (by decide) (by decide) with h346 | h346
              · linarith only [h0, h342, h346, h5, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h348 | h348
                · linarith only [h345, h346, h348, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h350 | h350
                  · linarith only [h0, h342, h350, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h2, h341, h345, h346, h348, h350, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h353 | h353
              · linarith only [h1, h353, h5, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h355 | h355
                · rcases m.htr 2 3 4 (by decide) (by decide) with h356 | h356
                  · linarith only [h0, h342, h345, h356, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h358 | h358
                    · linarith only [h1, h342, h358, h5, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h360 | h360
                      · linarith only [h0, h343, h360, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h0, h343, h355, h360, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h363 | h363
                  · linarith only [h342, h345, h363, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h365 | h365
                    · linarith only [h341, h342, h345, h355, h365, h5, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h367 | h367
                      · linarith only [h0, h342, h343, h345, h355, h367, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h369 | h369
                        · rcases h5bigk with h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [hlam, p370_0]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h3, hc15, hlam, hphi, ht01, ht0b, ht5b, p370_1, u1elo0]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p370_1, u2elo0]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h5, hlam, p370_0]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h342, h345, h355, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p370_1, u2elo0]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h3, hlam, p370_0]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [hlam, p370_0]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p370_1, u1elo4]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h353, hlam, p370_0]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h355, hlam, p370_0]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h4, hlam, p370_1]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h344, hlam, p370_1]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [hlam, p370_0]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h365, hlam, p370_1]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h367, hlam, p370_0]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h1, h342, h5, hc23, hc35, hlam, hphi, p370_1]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h342, h353, hc23, hc35, hlam, hphi, p370_1]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h365, hc23, hc35, hlam, hphi, p370_1]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [hlam, p370_0]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h342, h345, h355, h369, hc23, hc34, hlam, hphi, p370_1]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h341, hlam, p370_1]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h342, h345, h355, hc23, hc45, hlam, hphi, ht34, p370_1]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h2, h341, h363, h367, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p370_1, u1elo0]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [h369, hlam, p370_1]
                          · have p370_0 := h370c.1
                            have p370_1 := h370c.2.1
                            have p370_2 := h370c.2.2.1
                            have p370_3 := h370c.2.2.2
                            linarith only [hlam, p370_0]
                        · linarith only [h2, h341, h342, h345, h369, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · linarith only [h344, h4, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h398 | h398
          · rcases m.htr 1 3 4 (by decide) (by decide) with h399 | h399
            · linarith only [h342, h343, h399, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h401 | h401
              · linarith only [h342, h343, h401, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h403 | h403
                · rcases m.htr 2 3 4 (by decide) (by decide) with h404 | h404
                  · linarith only [h2, h342, h343, h399, h404, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h406 | h406
                    · linarith only [h1, h342, h406, h5, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h408 | h408
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h409 | h409
                        · rcases h5bigk with h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [hlam, p410_0]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h3, h342, h401, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p410_1, u1elo0]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p410_1, u2elo0]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h5, hlam, p410_0]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h3, hc45, hlam, hphi, ht01, ht0b, ht5b, p410_1, u1elo0]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h3, hlam, p410_0]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [hlam, p410_0]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h408, hc45, hlam, hphi, ht01, ht0b, ht5b, p410_1, u1elo4]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h401, hlam, p410_0]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h2, h343, h398, hc45, hlam, hphi, ht01, ht0b, ht5b, p410_1, u1elo0]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h4, hlam, p410_1]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h398, hlam, p410_1]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [hlam, p410_0]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h406, hlam, p410_1]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p410_1, u2elo4]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h1, h342, h5, hc23, hc35, hlam, hphi, p410_1]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h342, h401, hc23, hc35, hlam, hphi, p410_1]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h406, hc23, hc35, hlam, hphi, p410_1]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [hlam, p410_0]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            rcases p410_3 (m.d 0 5) (by simp) with h430 | h430
                            · linarith only [h430, h5, hlam]
                            · linarith only [h341, h430, hlam]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h341, hlam, p410_1]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h403, hlam, p410_1]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h408, hlam, p410_1]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [h409, hlam, p410_1]
                          · have p410_0 := h410c.1
                            have p410_1 := h410c.2.1
                            have p410_2 := h410c.2.2.1
                            have p410_3 := h410c.2.2.2
                            linarith only [hlam, p410_0]
                        · linarith only [h2, h341, h342, h399, h409, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h3, h343, h403, h408, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h2, h341, h342, h343, h403, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · linarith only [h342, h398, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h442 | h442
        · rcases m.htr 1 2 5 (by decide) (by decide) with h443 | h443
          · rcases m.htr 1 3 4 (by decide) (by decide) with h444 | h444
            · rcases m.htr 1 3 5 (by decide) (by decide) with h445 | h445
              · linarith only [h1, h445, h5, hlam]
              · linarith only [h342, h443, h445, hlam]
            · linarith only [h342, h442, h444, hlam]
          · linarith only [h4, h442, h443, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h450 | h450
          · rcases m.htr 1 3 4 (by decide) (by decide) with h451 | h451
            · rcases m.htr 1 3 5 (by decide) (by decide) with h452 | h452
              · linarith only [h1, h452, h5, hlam]
              · linarith only [h442, h450, h451, h452, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h455 | h455
              · linarith only [h1, h455, h5, hlam]
              · linarith only [h342, h450, h455, hlam]
          · linarith only [h4, h450, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h459 | h459
      · rcases m.htr 1 2 4 (by decide) (by decide) with h460 | h460
        · rcases m.htr 1 2 5 (by decide) (by decide) with h461 | h461
          · rcases m.htr 1 3 4 (by decide) (by decide) with h462 | h462
            · rcases m.htr 1 3 5 (by decide) (by decide) with h463 | h463
              · linarith only [h1, h463, h5, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h465 | h465
                · linarith only [h2, h341, h465, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h467 | h467
                  · linarith only [h0, h459, h467, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1, h462, h467, h5, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h470 | h470
              · linarith only [h1, h470, h5, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h472 | h472
                · linarith only [h2, h341, h472, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h474 | h474
                  · linarith only [h0, h459, h462, h474, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h476 | h476
                    · linarith only [h1, h459, h476, h5, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h478 | h478
                      · linarith only [h2, h341, h460, h478, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h480 | h480
                        · rcases h5bigk with h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h3, h460, h472, h474, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p481_1, u1elo0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h4, h474, h478, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p481_1, u2elo0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h5, hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h341, hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h3, hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h474, h478, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p481_1, u1elo4]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h470, hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h472, hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h4, hlam, p481_1]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h461, hlam, p481_1]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h476, hlam, p481_1]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h478, hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h4, h474, h478, hc23, hc35, hlam, hphi, p481_1]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h461, h474, h478, hc23, hc35, hlam, hphi, p481_1]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h474, h478, hc23, hc35, hlam, hphi, p481_1]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h2, h341, h460, h474, h480, hc23, hc34, hlam, hphi, p481_1]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h2, h341, h460, h474, hc23, hc45, hlam, hphi, ht34, p481_1]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h461, h474, h478, hc23, hc45, hlam, hphi, ht34, p481_1]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h474, h478, hc23, hc45, hlam, hphi, ht34, p481_1]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h480, hlam, p481_1]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [hlam, p481_0]
                        · rcases h5bigk with h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [hlam, p507_0]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h3, h461, h474, h478, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p507_1, u1elo0]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h4, h474, h478, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p507_1, u2elo0]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h5, hlam, p507_0]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h341, hlam, p507_0]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h3, hlam, p507_0]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [hlam, p507_0]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h474, h478, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p507_1, u1elo4]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h470, hlam, p507_0]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h472, hlam, p507_0]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h4, hlam, p507_1]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h461, hlam, p507_1]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [hlam, p507_0]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h476, hlam, p507_1]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h478, hlam, p507_0]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h4, h474, h478, h480, hc23, hc45, hlam, hphi, ht34, p507_1]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h461, h474, h478, h480, hc23, hc45, hlam, hphi, ht34, p507_1]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h474, h478, h480, hc23, hc45, hlam, hphi, ht34, p507_1]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [hlam, p507_0]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h480, hlam, p507_0]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h2, h341, h460, h474, hc23, hc45, hlam, hphi, ht34, p507_1]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h461, h474, h478, hc23, hc45, hlam, hphi, ht34, p507_1]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h474, h478, hc23, hc45, hlam, hphi, ht34, p507_1]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [h5, hc03, hc45, hlam, hphi, ht34, p507_1]
                          · have p507_0 := h507c.1
                            have p507_1 := h507c.2.1
                            have p507_2 := h507c.2.2.1
                            have p507_3 := h507c.2.2.2
                            linarith only [hlam, p507_0]
          · linarith only [h4, h461, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h534 | h534
          · rcases m.htr 1 3 4 (by decide) (by decide) with h535 | h535
            · linarith only [h459, h460, h535, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h537 | h537
              · linarith only [h459, h460, h5, h537, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h539 | h539
                · linarith only [h2, h341, h539, hlam]
                · linarith only [h460, h534, h539, hlam]
          · linarith only [h4, h534, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h543 | h543
        · rcases m.htr 1 2 5 (by decide) (by decide) with h544 | h544
          · rcases m.htr 1 3 4 (by decide) (by decide) with h545 | h545
            · rcases m.htr 1 3 5 (by decide) (by decide) with h546 | h546
              · linarith only [h1, h5, h546, hlam]
              · linarith only [h459, h544, h546, hlam]
            · linarith only [h459, h543, h545, hlam]
          · linarith only [h4, h543, h544, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h551 | h551
          · rcases m.htr 1 3 4 (by decide) (by decide) with h552 | h552
            · rcases m.htr 1 3 5 (by decide) (by decide) with h553 | h553
              · linarith only [h1, h5, h553, hlam]
              · linarith only [h543, h551, h552, h553, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h556 | h556
              · linarith only [h1, h5, h556, hlam]
              · linarith only [h459, h551, h556, hlam]
          · linarith only [h4, h551, hc12, hlam, hphi, u2elo0]

end R2N4
