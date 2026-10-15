import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5348000 in
set_option maxHeartbeats 5348000 in
theorem r1l7_12_13_25_L_I_L_R_H_I_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
  · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
      · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
            · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                  · linarith only [h0, h12, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h12, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                  · linarith only [h0, h15, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h15, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h10, h9, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
              · linarith only [h1, h19, h4, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
                · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h22, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                    · linarith only [h19, h24, h7, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                        · rcases h5bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h19, h4, h6, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h1, h24, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h1, h19, h4, h6, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            rcases p28_3 (m.d 0 5) (by simp) with h33 | h33
                            · rcases p28_3 (m.d 1 5) (by simp) with h34 | h34
                              · linarith only [h2, h34, hlam]
                              · linarith only [h21, h34, hlam]
                            · linarith only [h33, h6, hlam]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h2, hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h21, h24, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h19, hlam, p28_1]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p28_1]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h3, hlam, p28_1]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h8, hlam, p28_1]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h24, hlam, p28_1]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h0, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p28_1]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h5, hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h1, h27, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p28_1]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h1, h27, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p28_1]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h1, h27, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p28_1]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h6, hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h21, hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h26, hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h27, hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [hlam, p28_0]
                        · linarith only [h1, h27, h4, h6, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h21, h22, h26, h9, hc34, hlam, hphi, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                  · linarith only [h19, h60, h7, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h62 | h62
                    · linarith only [h1, h21, h4, h6, h62, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h64 | h64
                      · linarith only [h21, h60, h64, h9, hc34, hlam, hphi, u3ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h66 | h66
                        · linarith only [h1, h21, h4, h66, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h1, h4, h6, h66, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
          · linarith only [h0, h3, h7, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
          · rcases m.htr 1 3 4 (by decide) (by decide) with h71 | h71
            · rcases m.htr 1 3 5 (by decide) (by decide) with h72 | h72
              · rcases m.htr 1 4 5 (by decide) (by decide) with h73 | h73
                · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h75 | h75
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h76 | h76
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                        · rcases h5bigk with h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [hlam, p78_0]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [h1, h4, h6, h70, h75, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p78_1, u3ehi4]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [h1, h4, h6, h75, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p78_1, u3ehi4]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [h1, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p78_1, u3ehi4]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            rcases p78_3 (m.d 0 5) (by simp) with h83 | h83
                            · rcases p78_3 (m.d 1 5) (by simp) with h84 | h84
                              · linarith only [h2, h84, hlam]
                              · linarith only [h73, h84, hlam]
                            · linarith only [h6, h83, hlam]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [h2, hlam, p78_0]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [hlam, p78_0]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [h75, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p78_1, u3ehi4]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [h7, h70, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p78_1, u3ehi4]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [h7, h70, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p78_1]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [h3, hlam, p78_1]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [h70, hlam, p78_1]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [hlam, p78_0]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p78_1, u3ehi4]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [h7, h70, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p78_1]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [h5, hlam, p78_0]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [h72, hlam, p78_0]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [h75, hlam, p78_0]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [hlam, p78_0]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [h1, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p78_1]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [h6, hlam, p78_0]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [h73, hlam, p78_0]
                          · have p78_0 := h78c.1
                            have p78_1 := h78c.2.1
                            have p78_2 := h78c.2.2.1
                            have p78_3 := h78c.2.2.2
                            linarith only [h76, hlam, p78_0]
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
                        · linarith only [h1, h71, h73, h77, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1, h71, h73, h74, h76, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h1, h5, h7, h70, h75, hc01, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1, h4, h7, h70, h72, h74, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h112 | h112
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h113 | h113
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h114 | h114
                      · linarith only [h0, h114, h70, h71, h73, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h116 | h116
                        · linarith only [h116, h71, h73, hlam]
                        · rcases h5bigk with h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h1, h116, h4, h6, h72, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p118_1, u3ehi3]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h1, h113, h116, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p118_1, u3ehi3]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h1, h116, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p118_1, u3ehi3]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h1, h4, h6, h71, h73, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p118_1, u3ehi3]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h2, hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p118_1]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h116, h7, h70, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p118_1, u3ehi3]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h73, hlam, p118_1]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h3, hlam, p118_1]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h70, hlam, p118_1]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h116, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p118_1, u3ehi3]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h114, hlam, p118_1]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h5, hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h72, hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h113, hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h116, hlam, p118_1]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h6, hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h1, h4, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p118_1]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h1, h4, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p118_1]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h1, h116, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p118_1, u3ehi3]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [hlam, p118_0]
                    · linarith only [h1, h113, h5, h7, h70, hc01, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h112, h7, h70, h71, h73, hlam]
              · linarith only [h71, h72, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h147 | h147
              · linarith only [h1, h147, h4, h71, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
              · linarith only [h147, h7, h70, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h150 | h150
            · rcases m.htr 1 3 5 (by decide) (by decide) with h151 | h151
              · rcases m.htr 1 4 5 (by decide) (by decide) with h152 | h152
                · rcases m.htr 2 3 4 (by decide) (by decide) with h153 | h153
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h154 | h154
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h155 | h155
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h156 | h156
                        · rcases h5bigk with h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h1, h151, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p157_1, u3ehi4]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h1, h4, h6, h70, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p157_1]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h1, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p157_1, u3ehi4]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            rcases p157_3 (m.d 0 5) (by simp) with h162 | h162
                            · rcases p157_3 (m.d 1 5) (by simp) with h163 | h163
                              · linarith only [h163, h2, hlam]
                              · linarith only [h152, h163, hlam]
                            · linarith only [h162, h6, hlam]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h2, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h70, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p157_1, u3ehi4]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h1, h150, h152, hc01, hc45, hlam, hphi, ht0b, ht5b, p157_1]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h3, hlam, p157_1]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h0, h3, hc01, hc15, hlam, hphi, ht0b, ht5b, p157_1]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p157_1, u3ehi4]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h0, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p157_1]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h5, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h151, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h154, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h151, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p157_1]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h6, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h152, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h155, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h156, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [hlam, p157_0]
                        · linarith only [h1, h150, h152, h156, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1, h150, h152, h153, h155, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h151, h154, h7, hlam]
                  · linarith only [h151, h153, h7, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h191 | h191
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h192 | h192
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h193 | h193
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h194 | h194
                        · linarith only [h1, h150, h151, h152, h194, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · rcases h5bigk with h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [hlam, p196_0]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h150, h152, h6, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p196_1, u3ehi3]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h1, h150, h152, h191, h193, h4, h6, h70, hc01, hc12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p196_1, u3ehi3]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h1, h194, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p196_1, u3ehi3]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h1, h150, h152, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p196_1, u3ehi3]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h2, hlam, p196_0]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [hlam, p196_0]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h70, hlam, p196_0]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h194, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p196_1, u3ehi3]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h152, hlam, p196_1]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h3, hlam, p196_1]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h0, h3, hc01, hc15, hlam, hphi, ht0b, ht5b, p196_1]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [hlam, p196_0]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h0, h194, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p196_1, u3ehi3]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h0, h150, h152, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p196_1, u3ehi3]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h5, hlam, p196_0]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h151, hlam, p196_0]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h192, hlam, p196_0]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [hlam, p196_0]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h194, hlam, p196_1]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h6, hlam, p196_0]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h151, h191, h193, h194, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p196_1, u3ehi3]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h193, hlam, p196_0]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [h191, h193, h194, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p196_1, u3ehi3]
                          · have p196_0 := h196c.1
                            have p196_1 := h196c.2.1
                            have p196_2 := h196c.2.2.1
                            have p196_3 := h196c.2.2.2
                            linarith only [hlam, p196_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h222 | h222
                        · linarith only [h1, h150, h193, h222, h70, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h5bigk with h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h1, h150, h152, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p224_1, u3ehi3]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h1, h4, h6, h70, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p224_1]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h1, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p224_1, u3ehi4]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h1, h150, h152, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p224_1, u3ehi3]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h2, hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h70, hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p224_1, u3ehi4]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h152, hlam, p224_1]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h3, hlam, p224_1]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h0, h3, hc01, hc15, hlam, hphi, ht0b, ht5b, p224_1]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p224_1, u3ehi4]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h193, hlam, p224_1]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h5, hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h151, hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h192, hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h222, hlam, p224_1]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h6, hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h150, h152, hc45, hlam, hphi, ht34, p224_1, u3ehi3]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h1, h4, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p224_1]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h1, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p224_1, u3ehi4]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [hlam, p224_0]
                    · linarith only [h1, h150, h192, h5, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h150, h191, h7, hlam]
              · linarith only [h150, h151, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h253 | h253
              · linarith only [h1, h150, h253, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h255 | h255
                · rcases m.htr 2 3 4 (by decide) (by decide) with h256 | h256
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h257 | h257
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h258 | h258
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h259 | h259
                        · rcases h5bigk with h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h1, h253, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p260_1, u3ehi1]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h1, h257, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p260_1, u3ehi4]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h1, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p260_1, u3ehi4]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            rcases p260_3 (m.d 0 5) (by simp) with h265 | h265
                            · rcases p260_3 (m.d 1 5) (by simp) with h266 | h266
                              · linarith only [h2, h266, hlam]
                              · linarith only [h255, h266, hlam]
                            · linarith only [h265, h6, hlam]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h2, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h70, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h253, hlam, p260_1]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p260_1]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h3, hlam, p260_1]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h0, h3, hc01, hc15, hlam, hphi, ht0b, ht5b, p260_1]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h0, h253, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p260_1, u3ehi1]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h0, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p260_1]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h5, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h253, hc35, hlam, hphi, p260_1, u3ehi1]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h257, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h256, h259, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p260_1]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h6, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h255, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h258, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h259, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [hlam, p260_0]
                        · linarith only [h1, h150, h259, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h150, h255, h256, h258, hlam]
                    · linarith only [h150, h256, h257, hc35, hlam, hphi, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h293 | h293
                    · linarith only [h256, h293, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h295 | h295
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h296 | h296
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
                            linarith only [h1, h253, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p297_1, u3ehi1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h1, h4, h6, h70, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h1, h293, h4, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            rcases p297_3 (m.d 0 5) (by simp) with h302 | h302
                            · rcases p297_3 (m.d 1 5) (by simp) with h303 | h303
                              · linarith only [h2, h303, hlam]
                              · linarith only [h255, h303, hlam]
                            · linarith only [h302, h6, hlam]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h2, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h70, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h253, hlam, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h3, hlam, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h0, h3, hc01, hc15, hlam, hphi, ht0b, ht5b, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h293, hlam, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h0, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h5, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h1, h253, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p297_1, u3ehi1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h1, h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h1, h296, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h6, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h255, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h295, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h296, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [hlam, p297_0]
                        · linarith only [h1, h150, h296, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h150, h255, h256, h295, h7, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h329 | h329
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h330 | h330
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h331 | h331
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h332 | h332
                        · linarith only [h150, h255, h329, h332, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h150, h331, h332, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h1, h150, h329, h331, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h150, h329, h330, hc35, hlam, hphi, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h337 | h337
                    · linarith only [h329, h337, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h339 | h339
                      · linarith only [h1, h150, h255, h329, h339, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h341 | h341
                        · linarith only [h1, h329, h339, h341, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h1, h150, h341, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h344 | h344
        · rcases m.htr 1 2 5 (by decide) (by decide) with h345 | h345
          · rcases m.htr 1 3 4 (by decide) (by decide) with h346 | h346
            · rcases m.htr 1 3 5 (by decide) (by decide) with h347 | h347
              · rcases m.htr 1 4 5 (by decide) (by decide) with h348 | h348
                · linarith only [h0, h344, h346, h348, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h350 | h350
                  · linarith only [h0, h344, h350, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h350, h4, h6, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h346, h347, hc35, hlam, hphi, u3ehi3]
            · linarith only [h346, h4, h6, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h3, h344, h345, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h356 | h356
          · rcases m.htr 1 3 4 (by decide) (by decide) with h357 | h357
            · rcases m.htr 1 3 5 (by decide) (by decide) with h358 | h358
              · rcases m.htr 1 4 5 (by decide) (by decide) with h359 | h359
                · linarith only [h1, h357, h359, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h361 | h361
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h362 | h362
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h363 | h363
                      · linarith only [h0, h356, h363, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h365 | h365
                        · linarith only [h365, h4, h6, hlam]
                        · rcases h5bigk with h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h358, h365, h6, hc45, hlam, hphi, ht34, p367_1, u3ehi3]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h362, h365, h6, hc45, hlam, hphi, ht34, p367_1, u3ehi3]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h365, h6, hc45, hlam, hphi, ht34, p367_1, u3ehi3]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h6, hlam, p367_1]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h2, hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p367_1]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h344, h356, h365, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p367_1, u3ehi3]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h359, hlam, p367_1]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h3, hlam, p367_1]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h356, hlam, p367_1]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h365, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p367_1, u3ehi3]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h363, hlam, p367_1]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h5, hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h358, hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h362, hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h365, hlam, p367_1]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h365, h5, hc45, hlam, hphi, ht34, p367_1, u3ehi3]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h358, h365, hc45, hlam, hphi, ht34, p367_1, u3ehi3]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h362, h365, hc45, hlam, hphi, ht34, p367_1, u3ehi3]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h365, hc45, hlam, hphi, ht34, p367_1, u3ehi3]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [hlam, p367_0]
                    · linarith only [h1, h344, h356, h362, h5, hc01, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h344, h356, h357, h359, h361, hlam]
              · linarith only [h1, h357, h358, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h357, h4, h6, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h397 | h397
            · rcases m.htr 1 3 5 (by decide) (by decide) with h398 | h398
              · rcases m.htr 1 4 5 (by decide) (by decide) with h399 | h399
                · linarith only [h1, h397, h399, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h401 | h401
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h402 | h402
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h403 | h403
                      · linarith only [h3, h403, h6, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h405 | h405
                        · linarith only [h2, h397, h399, h405, h6, hlam]
                        · rcases h5bigk with h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h397, h399, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p407_1, u3ehi3]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h0, h3, h356, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p407_1]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h0, h3, h405, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p407_1, u3ehi3]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h6, hlam, p407_1]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h2, hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h356, hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h405, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p407_1, u3ehi3]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h399, hlam, p407_1]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h3, hlam, p407_1]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h0, h3, hc01, hc15, hlam, hphi, ht0b, ht5b, p407_1]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h0, h3, h405, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p407_1, u3ehi3]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h403, hlam, p407_1]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h5, hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h398, hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h402, hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h405, hlam, p407_1]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h2, h398, h405, hc45, hlam, hphi, ht34, p407_1, u3ehi3]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h398, h405, hc45, hlam, hphi, ht34, p407_1, u3ehi3]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h356, hc12, hc45, hlam, hphi, ht23, ht34, p407_1]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h405, hc45, hlam, hphi, ht34, p407_1, u3ehi3]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [hlam, p407_0]
                    · linarith only [h1, h398, h402, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h344, h398, h401, hc34, hlam, hphi, u3ehi4]
              · linarith only [h397, h398, hc35, hlam, hphi, u3ehi3]
            · linarith only [h397, h4, h6, hc45, hlam, hphi, ht34, u3ehi1]
    · linarith only [h4, h5, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h438 | h438
    · linarith only [h4, h438, hc34, hlam, hphi, u3ehi4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h440 | h440
      · rcases m.htr 1 2 3 (by decide) (by decide) with h441 | h441
        · rcases m.htr 1 2 5 (by decide) (by decide) with h442 | h442
          · rcases m.htr 1 3 4 (by decide) (by decide) with h443 | h443
            · linarith only [h1, h4, h443, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h445 | h445
              · linarith only [h1, h4, h445, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h447 | h447
                · rcases m.htr 2 3 4 (by decide) (by decide) with h448 | h448
                  · linarith only [h0, h4, h441, h448, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h450 | h450
                    · linarith only [h1, h438, h441, h450, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h452 | h452
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h453 | h453
                        · rcases h5bigk with h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h440, h445, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p454_1, u3ehi1]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h438, h450, h453, hc34, hlam, hphi, p454_1, u3ehi2]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h438, hlam, p454_1]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            rcases p454_3 (m.d 0 5) (by simp) with h459 | h459
                            · rcases p454_3 (m.d 1 5) (by simp) with h460 | h460
                              · linarith only [h2, h460, hlam]
                              · linarith only [h447, h460, hlam]
                            · linarith only [h440, h459, hlam]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h2, hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h450, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p454_1, u3ehi2]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h445, hlam, p454_1]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h0, h442, hc01, hc45, hlam, hphi, ht0b, ht5b, p454_1]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h3, hlam, p454_1]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h442, hlam, p454_1]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h450, hlam, p454_1]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h0, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p454_1]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h438, h453, hc34, hlam, hphi, p454_1, u3ehi0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h441, h445, h453, hc34, hlam, hphi, p454_1, u3ehi2]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h450, h453, hc34, hlam, hphi, p454_1, u3ehi2]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            rcases p454_3 (m.d 0 5) (by simp) with h478 | h478
                            · linarith only [h438, h478, hlam]
                            · linarith only [h440, h478, hlam]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h440, hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h447, hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h452, hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [h453, hlam, p454_0]
                          · have p454_0 := h454c.1
                            have p454_1 := h454c.2.1
                            have p454_2 := h454c.2.2.1
                            have p454_3 := h454c.2.2.2
                            linarith only [hlam, p454_0]
                        · linarith only [h1, h4, h441, h453, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h4, h440, h448, h452, hc34, hlam, hphi, u3ehi2]
                · linarith only [h4, h440, h441, h443, h447, hc34, hlam, hphi, u3ehi2]
          · linarith only [h0, h3, h441, h442, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h490 | h490
          · rcases m.htr 1 3 4 (by decide) (by decide) with h491 | h491
            · linarith only [h1, h4, h491, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h493 | h493
              · linarith only [h1, h4, h493, hc34, hlam, hphi, u3ehi4]
              · linarith only [h441, h490, h493, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h496 | h496
            · linarith only [h1, h4, h496, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h498 | h498
              · linarith only [h1, h438, h498, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h500 | h500
                · rcases m.htr 2 3 4 (by decide) (by decide) with h501 | h501
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h502 | h502
                    · linarith only [h3, h438, h502, hlam]
                    · linarith only [h501, h502, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h505 | h505
                    · linarith only [h501, h505, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h507 | h507
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h508 | h508
                        · rcases h5bigk with h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [hlam, p509_0]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h440, h498, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p509_1, u3ehi1]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h0, h3, h490, h498, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p509_1, u3ehi1]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h438, hlam, p509_1]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            rcases p509_3 (m.d 0 5) (by simp) with h514 | h514
                            · rcases p509_3 (m.d 1 5) (by simp) with h515 | h515
                              · linarith only [h2, h515, hlam]
                              · linarith only [h500, h515, hlam]
                            · linarith only [h440, h514, hlam]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h2, hlam, p509_0]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [hlam, p509_0]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h490, hlam, p509_0]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h498, hlam, p509_1]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p509_1]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h3, hlam, p509_1]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h0, h3, hc01, hc15, hlam, hphi, ht0b, ht5b, p509_1]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [hlam, p509_0]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h505, hlam, p509_1]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h0, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p509_1]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h2, h498, hc35, hlam, hphi, p509_1, u3ehi1]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h498, hc35, hlam, hphi, p509_1, u3ehi1]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h490, h498, hc35, hlam, hphi, p509_1, u3ehi1]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [hlam, p509_0]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            rcases p509_3 (m.d 0 5) (by simp) with h533 | h533
                            · linarith only [h438, h533, hlam]
                            · linarith only [h440, h533, hlam]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h440, hlam, p509_0]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h500, hlam, p509_0]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h507, hlam, p509_0]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [h508, hlam, p509_0]
                          · have p509_0 := h509c.1
                            have p509_1 := h509c.2.1
                            have p509_2 := h509c.2.2.1
                            have p509_3 := h509c.2.2.2
                            linarith only [hlam, p509_0]
                        · linarith only [h1, h4, h508, hc45, hlam, hphi, ht34, u3ehi1]
                      · linarith only [h4, h440, h501, h507, hc34, hlam, hphi, u3ehi2]
                · linarith only [h4, h440, h496, h500, hc34, hlam, hphi, u3ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h544 | h544
        · rcases m.htr 1 2 5 (by decide) (by decide) with h545 | h545
          · rcases m.htr 1 3 4 (by decide) (by decide) with h546 | h546
            · linarith only [h1, h4, h546, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h548 | h548
              · linarith only [h1, h4, h440, h548, hc45, hlam, hphi, ht34, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h550 | h550
                · linarith only [h4, h440, h546, h550, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h552 | h552
                  · linarith only [h1, h4, h440, h544, h552, hc45, hlam, hphi, ht34, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h554 | h554
                    · linarith only [h0, h544, h554, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h556 | h556
                      · linarith only [h4, h440, h552, h556, hc34, hlam, hphi, u3ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h558 | h558
                        · linarith only [h1, h4, h440, h544, h558, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h1, h4, h544, h558, hc45, hlam, hphi, ht34, u3ehi2]
          · linarith only [h0, h3, h544, h545, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h562 | h562
          · rcases m.htr 1 3 4 (by decide) (by decide) with h563 | h563
            · linarith only [h1, h4, h563, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h565 | h565
              · linarith only [h1, h4, h565, hc34, hlam, hphi, u3ehi4]
              · linarith only [h544, h562, h565, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h568 | h568
            · linarith only [h1, h4, h568, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h570 | h570
              · linarith only [h1, h4, h440, h570, hc45, hlam, hphi, ht34, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h572 | h572
                · linarith only [h4, h440, h568, h572, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h574 | h574
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h575 | h575
                    · linarith only [h3, h438, h575, hlam]
                    · linarith only [h1, h4, h574, h575, hc35, hlam, hphi, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h578 | h578
                    · linarith only [h574, h578, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h580 | h580
                      · linarith only [h1, h4, h440, h574, h580, hc34, hlam, hphi, u3ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h582 | h582
                        · linarith only [h1, h4, h440, h582, hc34, hlam, hphi, u3ehi1]
                        · linarith only [h1, h4, h582, hc45, hlam, hphi, ht34, u3ehi1]

end R2N4
