import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_15_H_I_L_0_L_0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                        · linarith only [h0, h12, h5, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h11, h12, h5, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                        · linarith only [h11, h15, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · rcases h2bigk with h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17_1]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h0, h10, hc01, hc35, hlam, hphi, ht0b, ht5b, p17_1]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            rcases p17_3 (m.d 0 2) (by simp) with h21 | h21
                            · rcases p17_3 (m.d 1 2) (by simp) with h22 | h22
                              · linarith only [h0, h22, hlam]
                              · linarith only [h22, h6, hlam]
                            · linarith only [h21, hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            rcases p17_3 (m.d 0 2) (by simp) with h26 | h26
                            · rcases p17_3 (m.d 1 2) (by simp) with h27 | h27
                              · linarith only [h0, h27, hlam]
                              · linarith only [h27, h7, hlam]
                            · linarith only [h26, hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h0, hlam, p17_1]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h10, h15, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17_1]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h0, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p17_1]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p17_1]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h1, hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h5, hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p17_1, u3elo2]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h0, h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p17_1]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h2, hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h6, hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h9, hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h11, hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h3, hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h7, hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h10, hlam, p17_0]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [h9, hc34, hlam, hphi, ht45, p17_1, u5elo2]
                          · have p17_0 := h17c.1
                            have p17_1 := h17c.2.1
                            have p17_2 := h17c.2.2.1
                            have p17_3 := h17c.2.2.2
                            linarith only [hlam, p17_0]
                    · linarith only [h10, h9, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h4, h9, hc23, hlam, hphi, u3elo0]
                · linarith only [h4, h8, hc13, hlam, hphi, u3elo0]
              · linarith only [h3, h5, h7, hc23, hlam, hphi, ht34, ht45, u5elo0]
            · linarith only [h2, h4, h5, h6, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h56 | h56
            · rcases m.htr 1 2 5 (by decide) (by decide) with h57 | h57
              · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
                · rcases m.htr 2 3 4 (by decide) (by decide) with h59 | h59
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
                      · linarith only [h1, h5, h56, h61, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h63 | h63
                        · linarith only [h59, h61, h63, hlam]
                        · rcases h2bigk with h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [hlam, p65_0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h0, h57, h59, h61, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p65_1]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h0, h5, h57, h59, h61, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p65_1]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            rcases p65_3 (m.d 0 2) (by simp) with h69 | h69
                            · rcases p65_3 (m.d 1 2) (by simp) with h70 | h70
                              · linarith only [h0, h70, hlam]
                              · linarith only [h56, h70, hlam]
                            · linarith only [h69, hlam, p65_0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            rcases p65_3 (m.d 0 2) (by simp) with h74 | h74
                            · rcases p65_3 (m.d 1 2) (by simp) with h75 | h75
                              · linarith only [h0, h75, hlam]
                              · linarith only [h57, h75, hlam]
                            · linarith only [h74, hlam, p65_0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h0, hlam, p65_1]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [hlam, p65_0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h5, hlam, p65_0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h1, h5, h59, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p65_1, u3elo0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h1, h5, h59, h61, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p65_1, u3elo0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h1, hlam, p65_0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h1, hc12, hlam, hphi, ht23, p65_1, u3elo0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [hlam, p65_0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h1, h59, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p65_1, u3elo0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h1, h59, h61, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p65_1, u3elo0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h2, hlam, p65_0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h56, hlam, p65_0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h59, hlam, p65_0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [hlam, p65_0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h61, hlam, p65_0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h3, hlam, p65_0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h57, hlam, p65_0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h60, hlam, p65_0]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [h57, h59, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p65_1]
                          · have p65_0 := h65c.1
                            have p65_1 := h65c.2.1
                            have p65_2 := h65c.2.2.1
                            have p65_3 := h65c.2.2.2
                            linarith only [hlam, p65_0]
                    · linarith only [h5, h60, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h5, h56, h59, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · linarith only [h4, h58, hc13, hlam, hphi, u3elo0]
              · linarith only [h56, h57, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h103 | h103
              · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h106 | h106
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h107 | h107
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h108 | h108
                        · rcases h2bigk with h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h0, h103, h106, h108, hc01, hc45, hlam, hphi, ht0b, ht5b, p109_1]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h0, h103, h105, h106, h108, h56, hc01, hc45, hlam, hphi, ht0b, ht5b, p109_1]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h0, h103, h106, h108, h56, hc01, hc45, hlam, hphi, ht0b, ht5b, p109_1]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            rcases p109_3 (m.d 0 2) (by simp) with h114 | h114
                            · rcases p109_3 (m.d 1 2) (by simp) with h115 | h115
                              · linarith only [h0, h115, hlam]
                              · linarith only [h103, h115, hlam]
                            · linarith only [h114, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h0, hlam, p109_1]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h5, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h56, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h105, h106, h108, h56, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p109_1]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h1, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h1, hc12, hlam, hphi, ht23, p109_1, u3elo0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h1, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p109_1, u3elo0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h1, h106, h108, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p109_1, u3elo0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h2, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h103, h106, h108, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p109_1]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h105, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h106, h108, h2, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p109_1, u3elo0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h3, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h103, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h106, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h107, hlam, p109_1]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [hlam, p109_0]
                        · linarith only [h1, h103, h107, h108, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                      · linarith only [h107, h56, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h103, h106, h5, hc25, hlam, hphi, u5elo3]
                  · linarith only [h103, h104, h105, h5, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h104, h4, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h144 | h144
                · rcases m.htr 2 3 4 (by decide) (by decide) with h145 | h145
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h146 | h146
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h147 | h147
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h148 | h148
                        · rcases h2bigk with h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            rcases p149_3 (m.d 0 2) (by simp) with h151 | h151
                            · rcases p149_3 (m.d 1 2) (by simp) with h152 | h152
                              · linarith only [h0, h152, hlam]
                              · rcases p149_3 (m.d 2 3) (by simp) with h154 | h154
                                · linarith only [h1, h154, hlam]
                                · linarith only [h154, h5, hlam]
                            · linarith only [h0, h151, hlam]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h0, h144, h148, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p149_1]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h0, h1, h144, h148, h5, h56, hc01, hc12, hc45, hlam, hphi, ht0b, ht23, ht5b, p149_1, u3elo0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h0, h1, h103, h144, h148, h5, hc01, hc12, hc45, hlam, hphi, ht0b, ht23, ht5b, p149_1, u3elo0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h0, hlam, p149_1]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h5, hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h56, hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h103, hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h1, hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h1, hc12, hlam, hphi, ht23, p149_1, u3elo0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h1, h56, hc12, hlam, hphi, ht23, p149_1, u3elo0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h1, h103, hc12, hlam, hphi, ht23, p149_1, u3elo0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h2, hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p149_1]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h145, hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h103, h2, h4, hc12, hlam, hphi, ht23, p149_1, u3elo0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h3, hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p149_1]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h146, hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h147, hlam, p149_1]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [hlam, p149_0]
                        · rcases h2bigk with h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            rcases p181_3 (m.d 0 2) (by simp) with h183 | h183
                            · rcases p181_3 (m.d 1 2) (by simp) with h184 | h184
                              · linarith only [h0, h184, hlam]
                              · rcases p181_3 (m.d 2 3) (by simp) with h186 | h186
                                · linarith only [h1, h186, hlam]
                                · linarith only [h186, h5, hlam]
                            · linarith only [h0, h183, hlam]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h0, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p181_1]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h0, h56, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p181_1]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h0, h103, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p181_1]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h0, hlam, p181_1]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h5, hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h56, hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h103, hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h1, hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p181_1]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h1, h56, hc12, hlam, hphi, ht23, p181_1, u3elo0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h1, h103, hc12, hlam, hphi, ht23, p181_1, u3elo0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h2, hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p181_1]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h145, hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h103, h2, h4, hc12, hlam, hphi, ht23, p181_1, u3elo0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h3, hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p181_1]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h146, hlam, p181_0]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [h147, hlam, p181_1]
                          · have p181_0 := h181c.1
                            have p181_1 := h181c.2.1
                            have p181_2 := h181c.2.2.1
                            have p181_3 := h181c.2.2.2
                            linarith only [hlam, p181_0]
                      · linarith only [h147, h56, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h146, h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h145, h5, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h144, h4, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h217 | h217
          · rcases m.htr 1 2 4 (by decide) (by decide) with h218 | h218
            · rcases m.htr 1 2 5 (by decide) (by decide) with h219 | h219
              · rcases m.htr 1 3 4 (by decide) (by decide) with h220 | h220
                · linarith only [h220, h4, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h222 | h222
                  · linarith only [h1, h222, h4, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h224 | h224
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h225 | h225
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h226 | h226
                        · rcases h2bigk with h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [hlam, p227_0]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h0, h218, h222, h224, h226, hc01, hc45, hlam, hphi, ht0b, ht5b, p227_1]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h0, h224, h226, hc01, hc45, hlam, hphi, ht0b, ht5b, p227_1]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h0, h222, h224, h226, hc01, hc45, hlam, hphi, ht0b, ht5b, p227_1]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            rcases p227_3 (m.d 0 2) (by simp) with h232 | h232
                            · rcases p227_3 (m.d 1 2) (by simp) with h233 | h233
                              · linarith only [h0, h233, hlam]
                              · linarith only [h219, h233, hlam]
                            · linarith only [h232, hlam, p227_0]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h0, hlam, p227_1]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [hlam, p227_0]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h224, h226, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p227_1]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h0, h222, h224, h226, hc01, hc45, hlam, hphi, ht0b, ht5b, p227_1]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p227_1]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h1, hlam, p227_0]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h217, hlam, p227_0]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [hlam, p227_0]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h222, hlam, p227_1]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h1, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p227_1, u3elo3]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h2, hlam, p227_0]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h218, hlam, p227_0]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h0, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p227_1]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [hlam, p227_0]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h0, h218, h224, h226, hc01, hc45, hlam, hphi, ht0b, ht5b, p227_1]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h3, hlam, p227_0]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h219, hlam, p227_0]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h224, hlam, p227_0]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [h225, hlam, p227_1]
                          · have p227_0 := h227c.1
                            have p227_1 := h227c.2.1
                            have p227_2 := h227c.2.2.1
                            have p227_3 := h227c.2.2.2
                            linarith only [hlam, p227_0]
                        · linarith only [h226, h4, hc03, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h222, h224, h225, hc35, hlam, hphi, u5elo4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h259 | h259
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h260 | h260
                        · rcases h2bigk with h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h0, h217, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p261_1]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            rcases p261_3 (m.d 0 2) (by simp) with h264 | h264
                            · rcases p261_3 (m.d 1 2) (by simp) with h265 | h265
                              · linarith only [h0, h265, hlam]
                              · linarith only [h217, h265, hlam]
                            · linarith only [h264, hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h0, h259, hc01, hc45, hlam, hphi, ht0b, ht5b, p261_1]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            rcases p261_3 (m.d 0 2) (by simp) with h270 | h270
                            · rcases p261_3 (m.d 1 2) (by simp) with h271 | h271
                              · linarith only [h0, h271, hlam]
                              · linarith only [h219, h271, hlam]
                            · linarith only [h270, hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h0, hlam, p261_1]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p261_1]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h0, h259, hc01, hc45, hlam, hphi, ht0b, ht5b, p261_1]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h0, h224, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p261_1]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h1, hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h217, hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h222, hlam, p261_1]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h224, hlam, p261_1]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h2, hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h218, hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h0, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p261_1]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h2, h224, h4, hc23, hlam, hphi, p261_1, u3elo3]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h3, hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h219, hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h219, hc23, hlam, hphi, ht34, ht45, p261_1, u5elo1]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h259, hlam, p261_1]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [hlam, p261_0]
                        · linarith only [h1, h260, h4, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h296 | h296
                        · linarith only [h222, h259, h296, hc23, hlam, hphi, u3elo3]
                        · linarith only [h1, h296, h4, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h217, h219, h3, hc23, hlam, hphi, ht34, ht45, u5elo0]
            · linarith only [h2, h217, h218, h4, hc23, hlam, hphi, u3elo3]
          · linarith only [h1, h217, h4, hc12, hlam, hphi, ht23, u3elo3]
      · linarith only [h1, h3, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h303 | h303
      · rcases m.htr 0 3 4 (by decide) (by decide) with h304 | h304
        · linarith only [h1, h2, h304, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h306 | h306
          · rcases m.htr 1 2 4 (by decide) (by decide) with h307 | h307
            · linarith only [h0, h2, h307, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h309 | h309
              · rcases m.htr 1 3 4 (by decide) (by decide) with h310 | h310
                · linarith only [h304, h310, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h312 | h312
                  · linarith only [h0, h2, h306, h310, h312, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h0, h2, h306, h312, hc23, hlam, hphi, u3elo3]
              · linarith only [h306, h309, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h1, h2, h306, hc12, hc24, hlam, hphi]
      · linarith only [h1, h303, hc23, hlam, hphi, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h318 | h318
    · rcases m.htr 0 2 5 (by decide) (by decide) with h319 | h319
      · rcases m.htr 0 3 4 (by decide) (by decide) with h320 | h320
        · rcases m.htr 1 2 3 (by decide) (by decide) with h321 | h321
          · linarith only [h0, h1, h318, h321, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h323 | h323
            · rcases m.htr 1 2 5 (by decide) (by decide) with h324 | h324
              · rcases m.htr 1 3 4 (by decide) (by decide) with h325 | h325
                · rcases m.htr 2 3 4 (by decide) (by decide) with h326 | h326
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h327 | h327
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h328 | h328
                      · linarith only [h0, h1, h323, h328, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h330 | h330
                        · linarith only [h326, h328, h330, hlam]
                        · rcases h2bigk with h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [hlam, p332_0]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h1, h324, h326, h328, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p332_1, u3elo2]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h1, hlam, p332_0]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h1, h326, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p332_1, u3elo2]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h1, h326, h328, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p332_1, u3elo2]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h0, hlam, p332_1]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [hlam, p332_0]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h321, hlam, p332_0]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h321, h326, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p332_1, u3elo1]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h0, h1, h326, h328, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p332_1, u3elo2]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [hc02, hlam, hphi, ht23, p332_1, u3elo2]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [hc12, hlam, hphi, ht23, p332_1, u3elo2]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [hlam, p332_0]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h326, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p332_1, u3elo2]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h326, h328, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p332_1, u3elo2]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h318, hlam, p332_0]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h323, hlam, p332_0]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h326, hlam, p332_0]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [hlam, p332_0]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h328, hlam, p332_0]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h319, hlam, p332_0]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h324, hlam, p332_0]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h327, hlam, p332_0]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [h0, h324, h326, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p332_1]
                          · have p332_0 := h332c.1
                            have p332_1 := h332c.2.1
                            have p332_2 := h332c.2.2.1
                            have p332_3 := h332c.2.2.2
                            linarith only [hlam, p332_0]
                    · linarith only [h1, h327, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h1, h323, h326, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · linarith only [h1, h318, h320, h325, hc13, hlam, hphi, u3elo2]
              · linarith only [h323, h324, hc24, hlam, hphi, ht45, u5elo2]
            · linarith only [h1, h318, h323, hc12, hlam, hphi, ht23, u3elo2]
        · linarith only [h1, h318, h320, hlam]
      · linarith only [h318, h319, hc24, hlam, hphi, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h365 | h365
      · rcases m.htr 0 3 4 (by decide) (by decide) with h366 | h366
        · rcases m.htr 1 2 3 (by decide) (by decide) with h367 | h367
          · linarith only [h0, h1, h365, h367, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h369 | h369
            · linarith only [h0, h318, h369, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h371 | h371
              · rcases m.htr 1 3 4 (by decide) (by decide) with h372 | h372
                · rcases m.htr 2 3 4 (by decide) (by decide) with h373 | h373
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h374 | h374
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h375 | h375
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h376 | h376
                        · rcases h2bigk with h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [hlam, p377_0]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [h371, h374, h376, hc02, hc45, hlam, hphi, ht0b, ht5b, p377_1]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [h1, hlam, p377_0]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [h318, hlam, p377_0]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [h318, h373, h374, h376, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p377_1, u3elo2]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [h0, hlam, p377_1]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [hlam, p377_0]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [h367, hlam, p377_0]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [h369, hlam, p377_0]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [h0, h374, h376, hc01, hc45, hlam, hphi, ht0b, ht5b, p377_1]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [hc02, hlam, hphi, ht23, p377_1, u3elo2]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [hc12, hlam, hphi, ht23, p377_1, u3elo2]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [hlam, p377_0]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p377_1, u3elo2]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [h374, h376, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p377_1, u3elo2]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [h0, h371, h374, h376, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p377_1]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [h371, h374, h376, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p377_1]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [h373, hlam, p377_0]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [hlam, p377_0]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [h373, h374, h376, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p377_1, u3elo2]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [h365, hlam, p377_0]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [h371, hlam, p377_0]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [h374, hlam, p377_0]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [h375, hlam, p377_1]
                          · have p377_0 := h377c.1
                            have p377_1 := h377c.2.1
                            have p377_2 := h377c.2.2.1
                            have p377_3 := h377c.2.2.2
                            linarith only [hlam, p377_0]
                        · linarith only [h0, h1, h371, h375, h376, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · linarith only [h0, h318, h371, h374, h375, hc35, hlam, hphi, u5elo4]
                    · linarith only [h1, h374, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h1, h371, h373, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h366, h372, hc13, hlam, hphi, u3elo0]
              · linarith only [h1, h365, h371, hc12, hlam, hphi, ht23, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h409 | h409
          · linarith only [h0, h1, h366, h409, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h411 | h411
            · linarith only [h0, h318, h411, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h413 | h413
              · rcases m.htr 1 3 4 (by decide) (by decide) with h414 | h414
                · linarith only [h0, h1, h366, h413, h414, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h416 | h416
                  · linarith only [h414, h416, hc13, hlam, hphi, u3elo2]
                  · linarith only [h0, h1, h413, h416, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
              · linarith only [h1, h365, h413, hc12, hlam, hphi, ht23, u3elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h420 | h420
        · rcases m.htr 1 2 3 (by decide) (by decide) with h421 | h421
          · linarith only [h0, h1, h365, h421, hc03, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h423 | h423
            · linarith only [h0, h318, h365, h423, hc04, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h425 | h425
              · linarith only [h0, h365, h425, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h427 | h427
                · rcases m.htr 2 3 4 (by decide) (by decide) with h428 | h428
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h429 | h429
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h430 | h430
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h431 | h431
                        · rcases h2bigk with h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [hlam, p432_0]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [h365, hc12, hlam, hphi, ht23, ht34, ht45, p432_1, u5elo2]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [h1, hlam, p432_0]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [h318, hlam, p432_0]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [h365, hlam, p432_0]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [h0, hlam, p432_1]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [hlam, p432_0]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [h421, hlam, p432_0]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [h423, hlam, p432_0]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [h425, hlam, p432_0]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p432_1]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [hc12, hlam, hphi, ht23, p432_1, u3elo2]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [hlam, p432_0]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p432_1, u3elo2]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [h0, h365, hc12, hlam, hphi, ht23, p432_1, u3elo2]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p432_1]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p432_1]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [h428, hlam, p432_0]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [hlam, p432_0]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [h0, h365, h428, hc12, hlam, hphi, ht23, p432_1, u3elo2]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p432_1]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p432_1, u5elo2]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [h429, hlam, p432_0]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [h430, hlam, p432_1]
                          · have p432_0 := h432c.1
                            have p432_1 := h432c.2.1
                            have p432_2 := h432c.2.2.1
                            have p432_3 := h432c.2.2.2
                            linarith only [hlam, p432_0]
                        · rcases h2bigk with h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [hlam, p458_0]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [h1, hc12, hlam, hphi, ht23, p458_1, u3elo2]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [h1, hlam, p458_0]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [h318, hlam, p458_0]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [h365, hlam, p458_0]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [h0, hlam, p458_1]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [hlam, p458_0]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [h421, hlam, p458_0]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [h423, hlam, p458_0]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [h425, hlam, p458_0]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [hc02, hlam, hphi, ht23, p458_1, u3elo2]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [hc12, hlam, hphi, ht23, p458_1, u3elo2]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [hlam, p458_0]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [h430, h431, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p458_1, u3elo2]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p458_1, u3elo2]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p458_1]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p458_1]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [h428, hlam, p458_0]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [hlam, p458_0]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [h0, h365, h428, hc12, hlam, hphi, ht23, p458_1, u3elo2]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p458_1]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p458_1, u5elo2]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [h429, hlam, p458_0]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [h430, hlam, p458_1]
                          · have p458_0 := h458c.1
                            have p458_1 := h458c.2.1
                            have p458_2 := h458c.2.2.1
                            have p458_3 := h458c.2.2.2
                            linarith only [hlam, p458_0]
                      · linarith only [h0, h318, h430, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h0, h1, h429, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h1, h428, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h1, h420, h427, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h488 | h488
          · linarith only [h0, h1, h488, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h490 | h490
            · linarith only [h0, h365, h490, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h492 | h492
              · linarith only [h0, h365, h492, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h494 | h494
                · linarith only [h1, h420, h494, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h496 | h496
                  · linarith only [h494, h496, hc13, hlam, hphi, u3elo2]
                  · linarith only [h0, h1, h496, hc12, hlam, hphi, ht23, u3elo3]

end R2N4
