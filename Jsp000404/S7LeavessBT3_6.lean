import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sBT3_H_I_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0bigk := hb0.1
  have h5elo := hb5.1
  have h3elo := hb3.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                                · rcases h0bigk with h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [hlam, p16_0]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16_1]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [h1, h11, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p16_1]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [h15, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p16_1]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    rcases p16_3 (m.d 0 1) (by simp) with h21 | h21
                                    · rcases p16_3 (m.d 0 2) (by simp) with h22 | h22
                                      · linarith only [h0, h22, hlam]
                                      · linarith only [h22, h6, hlam]
                                    · linarith only [h21, h3, hlam]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [h0, hlam, p16_1]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [hlam, p16_0]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [h1, h11, h15, hc02, hc45, hlam, hphi, ht0b, ht5b, p16_1]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [h0, h11, h15, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p16_1]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    rcases p16_3 (m.d 0 1) (by simp) with h30 | h30
                                    · rcases p16_3 (m.d 0 2) (by simp) with h31 | h31
                                      · rcases p16_3 (m.d 0 3) (by simp) with h32 | h32
                                        · linarith only [h32, h4, hlam]
                                        · linarith only [h32, h8, hlam]
                                      · linarith only [h31, h6, hlam]
                                    · linarith only [h3, h30, hlam]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [h1, hlam, p16_1]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [h4, hlam, p16_0]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [hlam, p16_0]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [h11, h15, h2, hc03, hc45, hlam, hphi, ht0b, ht5b, p16_1]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p16_1, u3elo0]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [h2, hlam, p16_1]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [h5, hlam, p16_0]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [h7, hlam, p16_1]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [hlam, p16_0]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [h10, h14, h3, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p16_1, u3elo0]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [h3, hlam, p16_1]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [h6, hlam, p16_0]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [h8, hlam, p16_0]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [h9, hlam, p16_0]
                                  · have p16_0 := h16c.1
                                    have p16_1 := h16c.2.1
                                    have p16_2 := h16c.2.2.1
                                    have p16_3 := h16c.2.2.2
                                    linarith only [hlam, p16_0]
                                · linarith only [h15, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h14, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h11, h13, hc23, hlam, hphi, u3elo1]
                          · linarith only [h12, h8, hc13, hlam, hphi, ht34, ht45, u5elo0]
                        · linarith only [h11, h7, hc13, hlam, hphi, u3elo0]
                      · linarith only [h10, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h9, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h8, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h60 | h60
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h61 | h61
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h62 | h62
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h63 | h63
                        · linarith only [h60, h63, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h65 | h65
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                            · linarith only [h1, h65, h66, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h68 | h68
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h69 | h69
                                · rcases h0bigk with h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [hlam, p70_0]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h0, h62, hc01, hc25, hlam, hphi, ht0b, ht5b, p70_1]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h1, h65, h69, hc01, hc45, hlam, hphi, ht0b, ht5b, p70_1]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h1, h65, h69, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p70_1]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    rcases p70_3 (m.d 0 1) (by simp) with h75 | h75
                                    · rcases p70_3 (m.d 0 2) (by simp) with h76 | h76
                                      · linarith only [h0, h76, hlam]
                                      · linarith only [h6, h76, hlam]
                                    · linarith only [h3, h75, hlam]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h0, hlam, p70_1]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [hlam, p70_0]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h1, h65, h69, hc02, hc45, hlam, hphi, ht0b, ht5b, p70_1]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h0, h1, h65, h69, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p70_1]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    rcases p70_3 (m.d 0 1) (by simp) with h84 | h84
                                    · rcases p70_3 (m.d 0 2) (by simp) with h85 | h85
                                      · rcases p70_3 (m.d 0 3) (by simp) with h86 | h86
                                        · linarith only [h4, h86, hlam]
                                        · linarith only [h60, h86, hlam]
                                      · linarith only [h6, h85, hlam]
                                    · linarith only [h3, h84, hlam]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h1, hlam, p70_1]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h4, hlam, p70_0]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [hlam, p70_0]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h7, hlam, p70_0]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h3, h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p70_1, u3elo3]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h2, hlam, p70_1]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h5, hlam, p70_0]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h1, h65, h69, hc04, hc45, hlam, hphi, ht0b, ht5b, p70_1]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [hlam, p70_0]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h6, h68, h69, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p70_1, u3elo3]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h3, hlam, p70_1]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h6, hlam, p70_0]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h60, hlam, p70_0]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [h61, hlam, p70_0]
                                  · have p70_0 := h70c.1
                                    have p70_1 := h70c.2.1
                                    have p70_2 := h70c.2.2.1
                                    have p70_3 := h70c.2.2.2
                                    linarith only [hlam, p70_0]
                                · linarith only [h69, h7, hc04, hlam, hphi, ht45, u5elo4]
                              · linarith only [h1, h65, h68, h7, hc23, hlam, hphi, u3elo3]
                          · linarith only [h60, h65, hc13, hlam, hphi, ht34, ht45, u5elo0]
                      · linarith only [h62, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h61, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h60, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h6, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h113 | h113
              · rcases m.htr 0 3 4 (by decide) (by decide) with h114 | h114
                · linarith only [h114, h4, h5, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h116 | h116
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h117 | h117
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h118 | h118
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                        · linarith only [h114, h119, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h121 | h121
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                            · linarith only [h1, h114, h121, h122, h4, hc02, hc35, hlam, hphi, ht0b, ht5b]
                            · linarith only [h122, h4, h5, hc23, hlam, hphi, u3elo3]
                          · linarith only [h121, hc13, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h118, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h117, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h116, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h113, h4, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h130 | h130
            · rcases m.htr 0 2 5 (by decide) (by decide) with h131 | h131
              · rcases m.htr 0 3 4 (by decide) (by decide) with h132 | h132
                · rcases m.htr 0 3 5 (by decide) (by decide) with h133 | h133
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h135 | h135
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h136 | h136
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h137 | h137
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h138 | h138
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h139 | h139
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h140 | h140
                                · linarith only [h130, h138, h140, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                · linarith only [h140, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h130, h138, h139, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                            · linarith only [h138, h4, hc02, hlam, hphi, ht23, u3elo3]
                          · linarith only [h136, h137, hc34, hlam, hphi, ht45, u5elo3]
                        · linarith only [h132, h136, h4, hc13, hlam, hphi, u3elo2]
                      · linarith only [h135, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h134, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h133, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h130, h132, h4, hlam]
              · linarith only [h130, h131, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h152 | h152
              · rcases m.htr 0 3 4 (by decide) (by decide) with h153 | h153
                · rcases m.htr 0 3 5 (by decide) (by decide) with h154 | h154
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h155 | h155
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h156 | h156
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h157 | h157
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h158 | h158
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h160 | h160
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h161 | h161
                                · rcases h0bigk with h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [hlam, p162_0]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h0, h156, h160, h161, hc01, hc45, hlam, hphi, ht0b, ht5b, p162_1]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h1, h157, h161, hc01, hc45, hlam, hphi, ht0b, ht5b, p162_1]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h0, h130, h156, h160, h161, hc01, hc45, hlam, hphi, ht0b, ht5b, p162_1]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    rcases p162_3 (m.d 0 1) (by simp) with h167 | h167
                                    · rcases p162_3 (m.d 0 2) (by simp) with h168 | h168
                                      · linarith only [h0, h168, hlam]
                                      · linarith only [h152, h168, hlam]
                                    · linarith only [h167, h3, hlam]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h0, hlam, p162_1]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [hlam, p162_0]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h4, hlam, p162_1]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h130, hlam, p162_1]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h130, h159, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p162_1, u3elo2]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h1, hlam, p162_1]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h0, h156, hc03, hc25, hlam, hphi, ht0b, ht5b, p162_1]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [hlam, p162_0]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h0, h130, h156, h160, h161, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p162_1, u3elo2]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h152, h160, h161, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p162_1, u3elo2]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h2, hlam, p162_1]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h0, h156, h160, h161, hc04, hc45, hlam, hphi, ht0b, ht5b, p162_1]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h153, hlam, p162_1]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [hlam, p162_0]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h152, h153, h160, h161, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p162_1, u3elo2]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h3, hlam, p162_1]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h152, hlam, p162_0]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h154, hlam, p162_0]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [h155, hlam, p162_0]
                                  · have p162_0 := h162c.1
                                    have p162_1 := h162c.2.1
                                    have p162_2 := h162c.2.2.1
                                    have p162_3 := h162c.2.2.2
                                    linarith only [hlam, p162_0]
                                · linarith only [h161, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h160, h4, hc03, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h0, h156, h157, h159, h4, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h154, h157, h158, hc34, hlam, hphi, ht45, u5elo0]
                        · linarith only [h153, h157, hc13, hlam, hphi, u3elo0]
                      · linarith only [h156, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h155, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h154, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h200 | h200
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h201 | h201
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h202 | h202
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h203 | h203
                        · linarith only [h0, h153, h202, h203, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h205 | h205
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h206 | h206
                            · linarith only [h0, h153, h202, h206, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                            · linarith only [h0, h202, h206, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                          · linarith only [h205, hc13, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h202, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h152, h153, h201, h4, hc25, hlam, hphi, u5elo4]
                  · linarith only [h152, h200, h4, hc25, hlam, hphi, u5elo3]
              · linarith only [h152, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h215 | h215
        · rcases m.htr 0 2 3 (by decide) (by decide) with h216 | h216
          · rcases m.htr 0 2 4 (by decide) (by decide) with h217 | h217
            · linarith only [h0, h2, h217, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h219 | h219
              · rcases m.htr 0 3 4 (by decide) (by decide) with h220 | h220
                · linarith only [h1, h2, h220, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h222 | h222
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h223 | h223
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h224 | h224
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h225 | h225
                        · linarith only [h220, h225, hc03, hlam, hphi, u3elo1]
                        · linarith only [h0, h2, h224, h225, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h224, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h2, h223, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h222, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h219, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h232 | h232
            · linarith only [h0, h2, h216, h232, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h234 | h234
              · rcases m.htr 0 3 4 (by decide) (by decide) with h235 | h235
                · linarith only [h1, h2, h235, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h237 | h237
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h238 | h238
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h239 | h239
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h240 | h240
                        · linarith only [h216, h235, h240, hc02, hlam, hphi, ht23, u3elo1]
                        · linarith only [h0, h2, h239, h240, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h239, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h2, h238, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h216, h237, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h234, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h215, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h249 | h249
    · rcases m.htr 0 1 4 (by decide) (by decide) with h250 | h250
      · rcases m.htr 0 1 5 (by decide) (by decide) with h251 | h251
        · rcases m.htr 0 2 3 (by decide) (by decide) with h252 | h252
          · rcases m.htr 0 2 4 (by decide) (by decide) with h253 | h253
            · rcases m.htr 0 2 5 (by decide) (by decide) with h254 | h254
              · rcases m.htr 0 3 4 (by decide) (by decide) with h255 | h255
                · rcases m.htr 0 3 5 (by decide) (by decide) with h256 | h256
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h257 | h257
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h258 | h258
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h259 | h259
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h260 | h260
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h261 | h261
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h262 | h262
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h263 | h263
                                · linarith only [h0, h249, h259, h263, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h263, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h262, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h255, h261, hc23, hlam, hphi, u3elo0]
                          · linarith only [h260, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h255, h259, hc13, hlam, hphi, u3elo0]
                      · linarith only [h0, h258, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h257, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h256, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h273 | h273
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h274 | h274
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h275 | h275
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h276 | h276
                        · linarith only [h249, h255, h276, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h278 | h278
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h279 | h279
                            · linarith only [h249, h255, h278, h279, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h281 | h281
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h282 | h282
                                · rcases h0bigk with h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [hlam, p283_0]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h0, hlam, p283_0]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h249, h278, h282, hc01, hc45, hlam, hphi, ht0b, ht5b, p283_1]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h0, h249, h255, h278, h282, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p283_1]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p283_1]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p283_1]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [hlam, p283_0]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h0, h249, h278, h282, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p283_1]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h0, h249, h255, h278, h282, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p283_1]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    rcases p283_3 (m.d 0 1) (by simp) with h293 | h293
                                    · linarith only [h0, h293, hlam]
                                    · linarith only [h251, h293, hlam]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h249, hlam, p283_1]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h252, hlam, p283_0]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [hlam, p283_0]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h255, hlam, p283_0]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h251, h255, h275, h281, h282, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p283_1, u3elo3]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h250, hlam, p283_1]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h253, hlam, p283_0]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h249, h278, h282, hc04, hc45, hlam, hphi, ht0b, ht5b, p283_1]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [hlam, p283_0]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h251, h255, h275, h281, h282, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p283_1, u3elo3]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h251, hlam, p283_1]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h254, hlam, p283_0]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h273, hlam, p283_0]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [h274, hlam, p283_0]
                                  · have p283_0 := h283c.1
                                    have p283_1 := h283c.2.1
                                    have p283_2 := h283c.2.2.1
                                    have p283_3 := h283c.2.2.2
                                    linarith only [hlam, p283_0]
                                · linarith only [h255, h282, hc04, hlam, hphi, ht45, u5elo4]
                              · linarith only [h249, h255, h278, h281, hc23, hlam, hphi, u3elo3]
                          · linarith only [h273, h278, hc13, hlam, hphi, ht34, ht45, u5elo0]
                      · linarith only [h0, h275, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h274, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h273, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h0, h249, h254, hc13, hlam, hphi, ht34, ht45, u5elo2]
            · linarith only [h0, h250, h253, hlam]
          · linarith only [h0, h249, h252, hc13, hlam, hphi, u3elo2]
        · linarith only [h249, h251, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h321 | h321
        · rcases m.htr 0 2 3 (by decide) (by decide) with h322 | h322
          · rcases m.htr 0 2 4 (by decide) (by decide) with h323 | h323
            · rcases m.htr 0 2 5 (by decide) (by decide) with h324 | h324
              · rcases m.htr 0 3 4 (by decide) (by decide) with h325 | h325
                · linarith only [h249, h250, h325, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h327 | h327
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h328 | h328
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h329 | h329
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h330 | h330
                        · linarith only [h0, h249, h325, h330, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h249, h250, h330, hc13, hlam, hphi, u3elo3]
                      · linarith only [h329, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h328, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h327, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h249, h250, h323, h324, hc13, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h337 | h337
              · rcases m.htr 0 3 4 (by decide) (by decide) with h338 | h338
                · linarith only [h0, h249, h323, h338, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h340 | h340
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h341 | h341
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h342 | h342
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h343 | h343
                        · linarith only [h338, h343, hc03, hlam, hphi, u3elo1]
                        · linarith only [h249, h250, h343, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h249, h342, hc13, hlam, hphi, ht34, ht45, u5elo2]
                    · linarith only [h0, h249, h323, h341, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h340, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h0, h249, h337, hc13, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h0, h249, h322, hc13, hlam, hphi, u3elo2]
        · linarith only [h249, h321, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h352 | h352
      · rcases m.htr 0 1 5 (by decide) (by decide) with h353 | h353
        · rcases m.htr 0 2 3 (by decide) (by decide) with h354 | h354
          · rcases m.htr 0 2 4 (by decide) (by decide) with h355 | h355
            · rcases m.htr 0 2 5 (by decide) (by decide) with h356 | h356
              · rcases m.htr 0 3 4 (by decide) (by decide) with h357 | h357
                · rcases m.htr 0 3 5 (by decide) (by decide) with h358 | h358
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h359 | h359
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h360 | h360
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h361 | h361
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h362 | h362
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h363 | h363
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h364 | h364
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h365 | h365
                                · linarith only [h249, h352, h361, h365, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                · linarith only [h365, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h364, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h357, h363, hc23, hlam, hphi, u3elo0]
                          · linarith only [h249, h362, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h249, h352, h361, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h0, h360, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h359, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h358, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h249, h352, h357, hlam]
              · linarith only [h249, h352, h354, h356, hc14, hlam, hphi, ht45, u5elo2]
            · linarith only [h249, h352, h354, h355, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h378 | h378
            · rcases m.htr 0 2 5 (by decide) (by decide) with h379 | h379
              · rcases m.htr 0 3 4 (by decide) (by decide) with h380 | h380
                · rcases m.htr 0 3 5 (by decide) (by decide) with h381 | h381
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h382 | h382
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h383 | h383
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h384 | h384
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h385 | h385
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h386 | h386
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h387 | h387
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h388 | h388
                                · linarith only [h249, h352, h384, h388, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                · linarith only [h388, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h0, h354, h387, hc01, hlam, hphi, ht12, ht23, u3elo4]
                            · linarith only [h0, h354, h386, hc01, hlam, hphi, ht12, ht23, u3elo3]
                          · linarith only [h249, h385, hc03, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h249, h352, h384, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h0, h352, h383, hc14, hlam, hphi, ht45, u5elo2]
                    · linarith only [h382, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h0, h352, h354, h381, hc14, hlam, hphi, ht45, u5elo3]
                · linarith only [h0, h352, h354, h380, hlam]
              · linarith only [h0, h352, h379, hc14, hlam, hphi, ht45, u5elo2]
            · linarith only [h0, h352, h378, hlam]
        · linarith only [h352, h353, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h402 | h402
        · rcases m.htr 0 2 3 (by decide) (by decide) with h403 | h403
          · rcases m.htr 0 2 4 (by decide) (by decide) with h404 | h404
            · rcases m.htr 0 2 5 (by decide) (by decide) with h405 | h405
              · rcases m.htr 0 3 4 (by decide) (by decide) with h406 | h406
                · rcases m.htr 0 3 5 (by decide) (by decide) with h407 | h407
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h408 | h408
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h409 | h409
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h410 | h410
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h411 | h411
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h412 | h412
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h413 | h413
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h414 | h414
                                · rcases h0bigk with h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [hlam, p415_0]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h0, hlam, p415_0]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h249, hlam, p415_0]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h352, hlam, p415_0]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h352, h410, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p415_1]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p415_1]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [hlam, p415_0]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h0, h403, h412, h414, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p415_1]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h0, h352, h402, h409, h413, h414, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p415_1]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    rcases p415_3 (m.d 0 1) (by simp) with h425 | h425
                                    · linarith only [h0, h425, hlam]
                                    · linarith only [h402, h425, hlam]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h402, h409, h413, h414, hc03, hc45, hlam, hphi, ht0b, ht5b, p415_1]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h403, hlam, p415_0]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [hlam, p415_0]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h249, h352, h402, h409, h413, h414, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p415_1, u3elo1]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h249, h402, h409, h413, h414, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p415_1, u3elo1]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h402, h409, h413, h414, hc04, hc45, hlam, hphi, ht0b, ht5b, p415_1]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h404, hlam, p415_0]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h406, hlam, p415_1]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [hlam, p415_0]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h352, h402, h409, h410, h413, h414, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p415_1, u3elo1]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h402, hlam, p415_1]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h405, hlam, p415_0]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h407, hlam, p415_0]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [h408, hlam, p415_0]
                                  · have p415_0 := h415c.1
                                    have p415_1 := h415c.2.1
                                    have p415_2 := h415c.2.2.1
                                    have p415_3 := h415c.2.2.2
                                    linarith only [hlam, p415_0]
                                · linarith only [h414, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h412, h413, hc34, hlam, hphi, ht45, u5elo3]
                            · linarith only [h249, h406, h412, hc23, hlam, hphi, u3elo1]
                          · linarith only [h352, h410, h411, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h249, h402, h406, h409, h410, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h409, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h408, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h352, h406, h407, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h451 | h451
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h452 | h452
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h453 | h453
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h454 | h454
                        · linarith only [h406, h454, hc03, hlam, hphi, u3elo1]
                        · linarith only [h249, h402, h453, h454, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h0, h453, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h249, h402, h406, h452, hc15, hlam, hphi, u5elo4]
                  · linarith only [h249, h402, h451, hc15, hlam, hphi, u5elo3]
              · linarith only [h403, h405, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h461 | h461
              · rcases m.htr 0 3 4 (by decide) (by decide) with h462 | h462
                · linarith only [h403, h404, h462, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h464 | h464
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h465 | h465
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h466 | h466
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h467 | h467
                        · linarith only [h249, h402, h462, h466, h467, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                        · linarith only [h249, h402, h466, h467, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h0, h466, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h403, h404, h465, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h249, h464, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h403, h461, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h474 | h474
            · rcases m.htr 0 2 5 (by decide) (by decide) with h475 | h475
              · rcases m.htr 0 3 4 (by decide) (by decide) with h476 | h476
                · rcases m.htr 0 3 5 (by decide) (by decide) with h477 | h477
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h478 | h478
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h479 | h479
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h480 | h480
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h481 | h481
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h482 | h482
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h483 | h483
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h484 | h484
                                · linarith only [h403, h474, h482, h484, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                · linarith only [h484, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h352, h403, h474, h483, hc01, hlam, hphi, ht12, ht23, u3elo4]
                            · linarith only [h352, h403, h474, h482, hc01, hlam, hphi, ht12, ht23, u3elo3]
                          · linarith only [h249, h481, hc03, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h249, h476, h480, hlam]
                      · linarith only [h0, h479, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h478, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h477, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h403, h474, h476, hlam]
              · linarith only [h352, h402, h474, h475, hc15, hlam, hphi, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h496 | h496
              · rcases m.htr 0 3 4 (by decide) (by decide) with h497 | h497
                · rcases m.htr 0 3 5 (by decide) (by decide) with h498 | h498
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h499 | h499
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h500 | h500
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h501 | h501
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h502 | h502
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h503 | h503
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h504 | h504
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h505 | h505
                                · rcases h0bigk with h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [hlam, p506_0]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h0, hlam, p506_0]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h249, hlam, p506_0]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h352, hlam, p506_0]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p506_1]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h474, hc01, hc24, hlam, hphi, ht12, p506_1]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [hlam, p506_0]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h403, hlam, p506_1]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h474, hlam, p506_1]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h402, h403, h500, h504, h505, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p506_1, u3elo2]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h249, h402, h500, h504, h505, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p506_1, u3elo1]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h249, hc02, hlam, hphi, ht23, p506_1, u3elo1]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [hlam, p506_0]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h0, h249, h402, h474, h500, h504, h505, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p506_1, u3elo1]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h249, h402, h500, h504, h505, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p506_1, u3elo1]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h402, h500, h504, h505, hc04, hc45, hlam, hphi, ht0b, ht5b, p506_1]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h0, h402, h474, h500, h504, h505, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p506_1]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h497, hlam, p506_1]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [hlam, p506_0]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h249, h402, h497, h500, h504, h505, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p506_1, u3elo1]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h402, hlam, p506_1]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h496, hlam, p506_0]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h498, hlam, p506_0]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [h499, hlam, p506_0]
                                  · have p506_0 := h506c.1
                                    have p506_1 := h506c.2.1
                                    have p506_2 := h506c.2.2.1
                                    have p506_3 := h506c.2.2.2
                                    linarith only [hlam, p506_0]
                                · linarith only [h505, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h504, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h0, h402, h403, h500, h503, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                          · linarith only [h352, h402, h500, h501, h502, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                        · linarith only [h497, h501, hc13, hlam, hphi, u3elo0]
                      · linarith only [h0, h402, h500, hc15, hlam, hphi, u5elo2]
                    · linarith only [h499, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h498, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h540 | h540
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h541 | h541
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h542 | h542
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h543 | h543
                        · linarith only [h0, h402, h403, h497, h542, h543, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                        · linarith only [h249, h402, h542, h543, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h0, h402, h542, hc15, hlam, hphi, u5elo2]
                    · linarith only [h0, h402, h403, h497, h541, hc15, hlam, hphi, u5elo4]
                  · linarith only [h0, h402, h403, h540, hc15, hlam, hphi, u5elo3]
              · linarith only [h0, h402, h496, hc15, hlam, hphi, u5elo2]
        · linarith only [h402, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem n7l_sBT3_H_I_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0bigk := hb0.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · rcases m.htr 0 1 2 (by decide) (by decide) with h8 | h8
              · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
                · linarith only [h5, h9, hlam]
                · linarith only [h8, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h8, hlam, p0_0]
            · linarith only [h7, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
            · rcases m.htr 0 1 2 (by decide) (by decide) with h15 | h15
              · rcases m.htr 0 1 3 (by decide) (by decide) with h16 | h16
                · linarith only [h16, h5, hlam]
                · linarith only [h16, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h15, hlam, p0_0]
            · linarith only [h14, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
            · rcases m.htr 0 1 2 (by decide) (by decide) with h23 | h23
              · rcases m.htr 0 1 3 (by decide) (by decide) with h24 | h24
                · rcases m.htr 0 1 4 (by decide) (by decide) with h25 | h25
                  · linarith only [h21, h25, hlam]
                  · linarith only [h25, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h23, h24, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h23, hlam, p0_0]
            · linarith only [h22, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h31 | h31
            · rcases m.htr 0 1 2 (by decide) (by decide) with h32 | h32
              · rcases m.htr 0 1 3 (by decide) (by decide) with h33 | h33
                · rcases m.htr 0 1 4 (by decide) (by decide) with h34 | h34
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h35 | h35
                    · linarith only [h31, h35, hlam]
                    · linarith only [h35, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h32, h34, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h32, h33, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h32, hlam, p0_0]
            · linarith only [h31, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · rcases p0_3 (m.d 0 2) (by simp) with h44 | h44
      · rcases p0_3 (m.d 0 3) (by simp) with h45 | h45
        · linarith only [h45, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h47 | h47
          · rcases p0_3 (m.d 0 5) (by simp) with h48 | h48
            · rcases m.htr 0 1 2 (by decide) (by decide) with h49 | h49
              · linarith only [h44, h49, hlam]
              · linarith only [h49, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h48, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h53 | h53
            · rcases m.htr 0 1 2 (by decide) (by decide) with h54 | h54
              · linarith only [h44, h54, hlam]
              · linarith only [h54, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h53, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h58 | h58
        · linarith only [h58, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h60 | h60
          · rcases p0_3 (m.d 0 5) (by simp) with h61 | h61
            · rcases m.htr 0 1 2 (by decide) (by decide) with h62 | h62
              · rcases m.htr 0 1 3 (by decide) (by decide) with h63 | h63
                · rcases m.htr 0 1 4 (by decide) (by decide) with h64 | h64
                  · linarith only [h60, h64, hlam]
                  · linarith only [h44, h64, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h63, hlam, p0_0]
              · linarith only [h44, h62, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h61, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h70 | h70
            · rcases m.htr 0 1 2 (by decide) (by decide) with h71 | h71
              · rcases m.htr 0 1 3 (by decide) (by decide) with h72 | h72
                · rcases m.htr 0 1 4 (by decide) (by decide) with h73 | h73
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h74 | h74
                    · linarith only [h70, h74, hlam]
                    · linarith only [h74, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h44, h71, h73, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h72, hlam, p0_0]
              · linarith only [h44, h71, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h70, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h43, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h82 | h82
    · rcases p0_3 (m.d 0 2) (by simp) with h83 | h83
      · rcases p0_3 (m.d 0 3) (by simp) with h84 | h84
        · rcases p0_3 (m.d 0 4) (by simp) with h85 | h85
          · linarith only [h85, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h87 | h87
            · rcases m.htr 0 1 2 (by decide) (by decide) with h88 | h88
              · linarith only [h83, h88, hlam]
              · linarith only [h88, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h87, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h92 | h92
          · linarith only [h92, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h94 | h94
            · rcases m.htr 0 1 2 (by decide) (by decide) with h95 | h95
              · linarith only [h83, h95, hlam]
              · linarith only [h84, h95, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h94, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h99 | h99
        · rcases p0_3 (m.d 0 4) (by simp) with h100 | h100
          · linarith only [h100, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h102 | h102
            · rcases m.htr 0 1 2 (by decide) (by decide) with h103 | h103
              · rcases m.htr 0 1 3 (by decide) (by decide) with h104 | h104
                · linarith only [h104, h99, hlam]
                · linarith only [h104, h83, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h103, h83, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h102, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h109 | h109
          · linarith only [h109, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h111 | h111
            · rcases m.htr 0 1 2 (by decide) (by decide) with h112 | h112
              · rcases m.htr 0 1 3 (by decide) (by decide) with h113 | h113
                · rcases m.htr 0 1 4 (by decide) (by decide) with h114 | h114
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h115 | h115
                    · linarith only [h111, h115, hlam]
                    · linarith only [h115, h99, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h114, hlam, p0_0]
                · linarith only [h112, h113, h83, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h112, h83, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h111, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h82, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h124 | h124
    · linarith only [h124, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h126 | h126
      · rcases p0_3 (m.d 0 3) (by simp) with h127 | h127
        · rcases p0_3 (m.d 0 4) (by simp) with h128 | h128
          · rcases p0_3 (m.d 0 5) (by simp) with h129 | h129
            · rcases m.htr 0 1 2 (by decide) (by decide) with h130 | h130
              · linarith only [h130, hlam, p0_0]
              · linarith only [h130, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h129, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h134 | h134
            · rcases m.htr 0 1 2 (by decide) (by decide) with h135 | h135
              · linarith only [h135, hlam, p0_0]
              · linarith only [h135, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h134, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h139 | h139
          · rcases p0_3 (m.d 0 5) (by simp) with h140 | h140
            · rcases m.htr 0 1 2 (by decide) (by decide) with h141 | h141
              · linarith only [h141, hlam, p0_0]
              · linarith only [h141, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h140, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h145 | h145
            · rcases m.htr 0 1 2 (by decide) (by decide) with h146 | h146
              · linarith only [h146, hlam, p0_0]
              · linarith only [h146, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h145, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h126, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h152 | h152
    · rcases p0_3 (m.d 0 2) (by simp) with h153 | h153
      · rcases p0_3 (m.d 0 3) (by simp) with h154 | h154
        · linarith only [h154, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h156 | h156
          · rcases p0_3 (m.d 0 5) (by simp) with h157 | h157
            · rcases m.htr 0 1 2 (by decide) (by decide) with h158 | h158
              · rcases m.htr 0 1 3 (by decide) (by decide) with h159 | h159
                · rcases m.htr 0 1 4 (by decide) (by decide) with h160 | h160
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h161 | h161
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h162 | h162
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h163 | h163
                        · linarith only [h156, h163, hlam]
                        · linarith only [h163, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h162, hlam, p0_0]
                    · linarith only [h158, h159, h161, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h158, h159, h160, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h158, h159, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h152, h158, hlam]
            · linarith only [h157, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h172 | h172
            · rcases m.htr 0 1 2 (by decide) (by decide) with h173 | h173
              · rcases m.htr 0 1 3 (by decide) (by decide) with h174 | h174
                · rcases m.htr 0 1 4 (by decide) (by decide) with h175 | h175
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h176 | h176
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h177 | h177
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h178 | h178
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h179 | h179
                          · linarith only [h172, h179, hlam]
                          · linarith only [h179, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                        · linarith only [h174, h178, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h177, hlam, p0_0]
                    · linarith only [h173, h174, h176, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h173, h174, h175, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h173, h174, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h152, h173, hlam]
            · linarith only [h152, h172, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h153, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h190 | h190
      · rcases p0_3 (m.d 0 3) (by simp) with h191 | h191
        · linarith only [h191, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h193 | h193
          · rcases p0_3 (m.d 0 5) (by simp) with h194 | h194
            · rcases m.htr 0 1 2 (by decide) (by decide) with h195 | h195
              · linarith only [h152, h195, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h152, h195, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h194, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h199 | h199
            · rcases m.htr 0 1 2 (by decide) (by decide) with h200 | h200
              · linarith only [h152, h200, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h152, h200, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h199, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h190, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h205 | h205
    · rcases p0_3 (m.d 0 2) (by simp) with h206 | h206
      · rcases p0_3 (m.d 0 3) (by simp) with h207 | h207
        · rcases p0_3 (m.d 0 4) (by simp) with h208 | h208
          · linarith only [h208, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h210 | h210
            · rcases m.htr 0 1 2 (by decide) (by decide) with h211 | h211
              · rcases m.htr 0 1 3 (by decide) (by decide) with h212 | h212
                · rcases m.htr 0 1 4 (by decide) (by decide) with h213 | h213
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h214 | h214
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h215 | h215
                      · linarith only [h207, h215, hlam]
                      · linarith only [h215, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h211, h213, h214, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h211, h213, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h211, h212, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h205, h211, hlam]
            · linarith only [h210, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h223 | h223
          · linarith only [h223, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h225 | h225
            · rcases m.htr 0 1 2 (by decide) (by decide) with h226 | h226
              · rcases m.htr 0 1 3 (by decide) (by decide) with h227 | h227
                · rcases m.htr 0 1 4 (by decide) (by decide) with h228 | h228
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h229 | h229
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h230 | h230
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h231 | h231
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h232 | h232
                          · linarith only [h225, h232, hlam]
                          · linarith only [h207, h232, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                        · linarith only [h231, hlam, p0_0]
                      · linarith only [h207, h227, h230, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h207, h226, h227, h229, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h207, h226, h227, h228, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h207, h226, h227, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h205, h226, hlam]
            · linarith only [h225, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h206, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h243 | h243
      · rcases p0_3 (m.d 0 3) (by simp) with h244 | h244
        · rcases p0_3 (m.d 0 4) (by simp) with h245 | h245
          · linarith only [h245, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h247 | h247
            · rcases m.htr 0 1 2 (by decide) (by decide) with h248 | h248
              · linarith only [h205, h248, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h205, h248, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h247, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h252 | h252
          · linarith only [h252, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h254 | h254
            · rcases m.htr 0 1 2 (by decide) (by decide) with h255 | h255
              · linarith only [h205, h255, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h205, h255, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h254, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h243, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h261 | h261
    · linarith only [h261, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h263 | h263
      · rcases p0_3 (m.d 0 3) (by simp) with h264 | h264
        · rcases p0_3 (m.d 0 4) (by simp) with h265 | h265
          · rcases p0_3 (m.d 0 5) (by simp) with h266 | h266
            · rcases m.htr 0 1 2 (by decide) (by decide) with h267 | h267
              · linarith only [h267, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h263, h267, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h263, h266, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h271 | h271
            · rcases m.htr 0 1 2 (by decide) (by decide) with h272 | h272
              · linarith only [h263, h272, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h263, h272, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h263, h271, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h264, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h277 | h277
        · rcases p0_3 (m.d 0 4) (by simp) with h278 | h278
          · rcases p0_3 (m.d 0 5) (by simp) with h279 | h279
            · rcases m.htr 0 1 2 (by decide) (by decide) with h280 | h280
              · linarith only [h280, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h263, h280, hlam]
            · linarith only [h279, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h284 | h284
            · rcases m.htr 0 1 2 (by decide) (by decide) with h285 | h285
              · linarith only [h285, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h263, h285, hlam]
            · linarith only [h284, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h277, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h290 | h290
    · rcases p0_3 (m.d 0 2) (by simp) with h291 | h291
      · linarith only [h291, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h293 | h293
        · rcases p0_3 (m.d 0 4) (by simp) with h294 | h294
          · rcases p0_3 (m.d 0 5) (by simp) with h295 | h295
            · rcases m.htr 0 1 2 (by decide) (by decide) with h296 | h296
              · rcases m.htr 0 1 3 (by decide) (by decide) with h297 | h297
                · rcases m.htr 0 1 4 (by decide) (by decide) with h298 | h298
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h299 | h299
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h300 | h300
                      · linarith only [h300, hlam, p0_0]
                      · linarith only [h300, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h296, h297, h299, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h296, h297, h298, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h290, h297, hlam]
              · linarith only [h290, h296, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h290, h295, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h308 | h308
            · rcases m.htr 0 1 2 (by decide) (by decide) with h309 | h309
              · rcases m.htr 0 1 3 (by decide) (by decide) with h310 | h310
                · rcases m.htr 0 1 4 (by decide) (by decide) with h311 | h311
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h312 | h312
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h313 | h313
                      · linarith only [h313, hlam, p0_0]
                      · linarith only [h313, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h309, h310, h312, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h309, h310, h311, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h290, h310, hlam]
              · linarith only [h290, h309, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h290, h308, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h293, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h322 | h322
      · linarith only [h322, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h324 | h324
        · rcases p0_3 (m.d 0 4) (by simp) with h325 | h325
          · rcases p0_3 (m.d 0 5) (by simp) with h326 | h326
            · rcases m.htr 0 1 2 (by decide) (by decide) with h327 | h327
              · linarith only [h290, h327, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h329 | h329
                · linarith only [h327, h329, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h327, h329, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h326, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h333 | h333
            · rcases m.htr 0 1 2 (by decide) (by decide) with h334 | h334
              · linarith only [h290, h334, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h336 | h336
                · linarith only [h334, h336, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h334, h336, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h333, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h324, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h342 | h342
    · rcases p0_3 (m.d 0 2) (by simp) with h343 | h343
      · rcases p0_3 (m.d 0 3) (by simp) with h344 | h344
        · rcases p0_3 (m.d 0 4) (by simp) with h345 | h345
          · linarith only [h345, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h347 | h347
            · rcases m.htr 0 1 2 (by decide) (by decide) with h348 | h348
              · rcases m.htr 0 1 3 (by decide) (by decide) with h349 | h349
                · rcases m.htr 0 1 4 (by decide) (by decide) with h350 | h350
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h351 | h351
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h352 | h352
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h353 | h353
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h354 | h354
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h355 | h355
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h356 | h356
                              · linarith only [h347, h356, hlam]
                              · linarith only [h350, h356, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                            · linarith only [h355, hlam, p0_0]
                          · linarith only [h350, h352, h354, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                        · linarith only [h350, h352, h353, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                      · linarith only [h343, h352, hlam]
                    · linarith only [h349, h350, h351, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h343, h348, h350, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h342, h349, hlam]
              · linarith only [h342, h348, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h342, h347, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h344, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h369 | h369
        · rcases p0_3 (m.d 0 4) (by simp) with h370 | h370
          · linarith only [h370, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h372 | h372
            · rcases m.htr 0 1 2 (by decide) (by decide) with h373 | h373
              · rcases m.htr 0 1 3 (by decide) (by decide) with h374 | h374
                · rcases m.htr 0 1 4 (by decide) (by decide) with h375 | h375
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h376 | h376
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h377 | h377
                      · linarith only [h343, h374, h377, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h343, h373, h377, hc12, hc23, hlam, hphi, p0_1]
                    · linarith only [h343, h373, h374, h376, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h343, h373, h374, h375, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h342, h374, hlam]
              · linarith only [h342, h343, h373, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h342, h372, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h369, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h386 | h386
      · rcases p0_3 (m.d 0 3) (by simp) with h387 | h387
        · rcases p0_3 (m.d 0 4) (by simp) with h388 | h388
          · linarith only [h388, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h390 | h390
            · rcases m.htr 0 1 2 (by decide) (by decide) with h391 | h391
              · linarith only [h342, h391, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h342, h386, h391, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h386, h390, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h387, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h396 | h396
        · rcases p0_3 (m.d 0 4) (by simp) with h397 | h397
          · linarith only [h397, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h399 | h399
            · rcases m.htr 0 1 2 (by decide) (by decide) with h400 | h400
              · linarith only [h342, h400, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h402 | h402
                · linarith only [h386, h400, h402, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h386, h400, h402, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h399, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h396, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h408 | h408
    · linarith only [h408, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h410 | h410
      · rcases p0_3 (m.d 0 3) (by simp) with h411 | h411
        · rcases p0_3 (m.d 0 4) (by simp) with h412 | h412
          · rcases p0_3 (m.d 0 5) (by simp) with h413 | h413
            · rcases m.htr 0 1 2 (by decide) (by decide) with h414 | h414
              · linarith only [h410, h414, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h410, h414, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h410, h413, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h412, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h419 | h419
          · rcases p0_3 (m.d 0 5) (by simp) with h420 | h420
            · rcases m.htr 0 1 2 (by decide) (by decide) with h421 | h421
              · linarith only [h410, h421, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h410, h421, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h410, h420, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h419, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h426 | h426
        · rcases p0_3 (m.d 0 4) (by simp) with h427 | h427
          · rcases p0_3 (m.d 0 5) (by simp) with h428 | h428
            · rcases m.htr 0 1 2 (by decide) (by decide) with h429 | h429
              · linarith only [h429, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h410, h429, hlam]
            · linarith only [h428, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h427, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h434 | h434
          · rcases p0_3 (m.d 0 5) (by simp) with h435 | h435
            · rcases m.htr 0 1 2 (by decide) (by decide) with h436 | h436
              · linarith only [h436, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h410, h436, hlam]
            · linarith only [h435, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h434, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h441 | h441
    · rcases p0_3 (m.d 0 2) (by simp) with h442 | h442
      · linarith only [h442, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h444 | h444
        · rcases p0_3 (m.d 0 4) (by simp) with h445 | h445
          · rcases p0_3 (m.d 0 5) (by simp) with h446 | h446
            · rcases m.htr 0 1 2 (by decide) (by decide) with h447 | h447
              · rcases m.htr 0 1 3 (by decide) (by decide) with h448 | h448
                · rcases m.htr 0 1 4 (by decide) (by decide) with h449 | h449
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h450 | h450
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h451 | h451
                      · linarith only [h444, h448, h451, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h444, h451, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h447, h449, h450, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h441, h449, hlam]
                · linarith only [h441, h447, h448, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h441, h447, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h441, h446, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h445, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h460 | h460
          · rcases p0_3 (m.d 0 5) (by simp) with h461 | h461
            · rcases m.htr 0 1 2 (by decide) (by decide) with h462 | h462
              · rcases m.htr 0 1 3 (by decide) (by decide) with h463 | h463
                · rcases m.htr 0 1 4 (by decide) (by decide) with h464 | h464
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h465 | h465
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h466 | h466
                      · linarith only [h464, h466, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h444, h466, hlam]
                    · linarith only [h464, h465, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h441, h464, hlam]
                · linarith only [h441, h462, h463, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h441, h462, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h441, h461, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h460, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h475 | h475
      · linarith only [h475, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h477 | h477
        · rcases p0_3 (m.d 0 4) (by simp) with h478 | h478
          · rcases p0_3 (m.d 0 5) (by simp) with h479 | h479
            · rcases m.htr 0 1 2 (by decide) (by decide) with h480 | h480
              · linarith only [h441, h480, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h482 | h482
                · linarith only [h480, h482, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h477, h480, h482, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h479, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h478, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h487 | h487
          · rcases p0_3 (m.d 0 5) (by simp) with h488 | h488
            · rcases m.htr 0 1 2 (by decide) (by decide) with h489 | h489
              · linarith only [h441, h489, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h491 | h491
                · linarith only [h489, h491, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h493 | h493
                  · linarith only [h489, h493, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h489, h493, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h488, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h487, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h498 | h498
    · rcases p0_3 (m.d 0 2) (by simp) with h499 | h499
      · rcases p0_3 (m.d 0 3) (by simp) with h500 | h500
        · linarith only [h500, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h502 | h502
          · rcases p0_3 (m.d 0 5) (by simp) with h503 | h503
            · rcases m.htr 0 1 2 (by decide) (by decide) with h504 | h504
              · rcases m.htr 0 1 3 (by decide) (by decide) with h505 | h505
                · rcases m.htr 0 1 4 (by decide) (by decide) with h506 | h506
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h507 | h507
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h508 | h508
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h509 | h509
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h510 | h510
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h511 | h511
                            · linarith only [h511, hlam, p0_0]
                            · linarith only [h505, h511, hc13, hc34, hlam, hphi, p0_1]
                          · linarith only [h505, h509, h510, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                        · linarith only [h499, h509, hlam]
                      · linarith only [h499, h505, h508, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h505, h506, h507, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h498, h506, hlam]
                · linarith only [h498, h505, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h498, h504, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h498, h503, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h502, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h523 | h523
        · linarith only [h523, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h525 | h525
          · rcases p0_3 (m.d 0 5) (by simp) with h526 | h526
            · rcases m.htr 0 1 2 (by decide) (by decide) with h527 | h527
              · rcases m.htr 0 1 3 (by decide) (by decide) with h528 | h528
                · rcases m.htr 0 1 4 (by decide) (by decide) with h529 | h529
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h530 | h530
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h531 | h531
                      · linarith only [h499, h531, hlam]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h533 | h533
                        · linarith only [h529, h531, h533, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                        · linarith only [h527, h531, h533, hc12, hc24, hlam, hphi, p0_1]
                    · linarith only [h529, h530, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h498, h529, hlam]
                · linarith only [h498, h499, h527, h528, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h498, h499, h527, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h498, h526, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h525, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h542 | h542
      · rcases p0_3 (m.d 0 3) (by simp) with h543 | h543
        · linarith only [h543, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h545 | h545
          · rcases p0_3 (m.d 0 5) (by simp) with h546 | h546
            · rcases m.htr 0 1 2 (by decide) (by decide) with h547 | h547
              · linarith only [h498, h547, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h498, h542, h547, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h542, h546, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h545, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h552 | h552
        · linarith only [h552, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h554 | h554
          · rcases p0_3 (m.d 0 5) (by simp) with h555 | h555
            · rcases m.htr 0 1 2 (by decide) (by decide) with h556 | h556
              · linarith only [h498, h556, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h558 | h558
                · linarith only [h498, h558, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h560 | h560
                  · linarith only [h542, h556, h560, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h542, h556, h560, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h555, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h554, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h567 | h567
    · linarith only [h567, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h569 | h569
      · rcases p0_3 (m.d 0 3) (by simp) with h570 | h570
        · rcases p0_3 (m.d 0 4) (by simp) with h571 | h571
          · rcases p0_3 (m.d 0 5) (by simp) with h572 | h572
            · rcases m.htr 0 1 2 (by decide) (by decide) with h573 | h573
              · linarith only [h569, h573, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h573, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h572, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h577 | h577
            · rcases m.htr 0 1 2 (by decide) (by decide) with h578 | h578
              · linarith only [h569, h578, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h578, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h577, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h582 | h582
          · rcases p0_3 (m.d 0 5) (by simp) with h583 | h583
            · rcases m.htr 0 1 2 (by decide) (by decide) with h584 | h584
              · linarith only [h569, h584, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h584, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h583, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h588 | h588
            · rcases m.htr 0 1 2 (by decide) (by decide) with h589 | h589
              · linarith only [h569, h589, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h589, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h588, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h593 | h593
        · rcases p0_3 (m.d 0 4) (by simp) with h594 | h594
          · rcases p0_3 (m.d 0 5) (by simp) with h595 | h595
            · rcases m.htr 0 1 2 (by decide) (by decide) with h596 | h596
              · linarith only [h593, h596, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h596, hlam]
            · linarith only [h595, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h600 | h600
            · rcases m.htr 0 1 2 (by decide) (by decide) with h601 | h601
              · linarith only [h593, h601, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h601, hlam]
            · linarith only [h600, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h605 | h605
          · rcases p0_3 (m.d 0 5) (by simp) with h606 | h606
            · rcases m.htr 0 1 2 (by decide) (by decide) with h607 | h607
              · linarith only [h605, h607, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h607, hlam]
            · linarith only [h606, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h611 | h611
            · rcases m.htr 0 1 2 (by decide) (by decide) with h612 | h612
              · linarith only [h612, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h569, h612, hlam]
            · linarith only [h611, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h616 | h616
    · rcases p0_3 (m.d 0 2) (by simp) with h617 | h617
      · linarith only [h617, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h619 | h619
        · rcases p0_3 (m.d 0 4) (by simp) with h620 | h620
          · rcases p0_3 (m.d 0 5) (by simp) with h621 | h621
            · rcases m.htr 0 1 2 (by decide) (by decide) with h622 | h622
              · rcases m.htr 0 1 3 (by decide) (by decide) with h623 | h623
                · rcases m.htr 0 1 4 (by decide) (by decide) with h624 | h624
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h625 | h625
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h626 | h626
                      · linarith only [h619, h623, h626, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h619, h626, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h616, h625, hlam]
                  · linarith only [h616, h622, h624, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h616, h622, h623, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h616, h622, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h621, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h634 | h634
            · rcases m.htr 0 1 2 (by decide) (by decide) with h635 | h635
              · rcases m.htr 0 1 3 (by decide) (by decide) with h636 | h636
                · rcases m.htr 0 1 4 (by decide) (by decide) with h637 | h637
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h638 | h638
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h639 | h639
                      · linarith only [h619, h636, h639, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h619, h639, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h616, h638, hlam]
                  · linarith only [h619, h635, h636, h637, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h616, h635, h636, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h616, h635, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h634, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h647 | h647
          · rcases p0_3 (m.d 0 5) (by simp) with h648 | h648
            · rcases m.htr 0 1 2 (by decide) (by decide) with h649 | h649
              · rcases m.htr 0 1 3 (by decide) (by decide) with h650 | h650
                · rcases m.htr 0 1 4 (by decide) (by decide) with h651 | h651
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h652 | h652
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h653 | h653
                      · linarith only [h647, h651, h653, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h619, h653, hlam]
                    · linarith only [h616, h652, hlam]
                  · linarith only [h616, h651, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h616, h649, h650, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h616, h649, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h648, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h661 | h661
            · rcases m.htr 0 1 2 (by decide) (by decide) with h662 | h662
              · rcases m.htr 0 1 3 (by decide) (by decide) with h663 | h663
                · rcases m.htr 0 1 4 (by decide) (by decide) with h664 | h664
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h665 | h665
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h666 | h666
                      · linarith only [h665, h666, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h619, h666, hlam]
                    · linarith only [h616, h665, hlam]
                  · linarith only [h616, h664, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h616, h662, h663, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h616, h662, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h661, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h674 | h674
      · linarith only [h674, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h676 | h676
        · rcases p0_3 (m.d 0 4) (by simp) with h677 | h677
          · rcases p0_3 (m.d 0 5) (by simp) with h678 | h678
            · rcases m.htr 0 1 2 (by decide) (by decide) with h679 | h679
              · linarith only [h616, h679, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h681 | h681
                · linarith only [h676, h679, h681, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h676, h679, h681, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h678, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h685 | h685
            · rcases m.htr 0 1 2 (by decide) (by decide) with h686 | h686
              · linarith only [h616, h686, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h688 | h688
                · linarith only [h676, h686, h688, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h676, h686, h688, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h685, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h692 | h692
          · rcases p0_3 (m.d 0 5) (by simp) with h693 | h693
            · rcases m.htr 0 1 2 (by decide) (by decide) with h694 | h694
              · linarith only [h616, h694, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h696 | h696
                · linarith only [h692, h694, h696, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h698 | h698
                  · linarith only [h692, h694, h698, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h692, h694, h698, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h693, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h702 | h702
            · rcases m.htr 0 1 2 (by decide) (by decide) with h703 | h703
              · linarith only [h616, h703, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h705 | h705
                · linarith only [h703, h705, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h707 | h707
                  · linarith only [h703, h707, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h709 | h709
                    · linarith only [h703, h709, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                    · linarith only [h703, h709, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h702, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h713 | h713
    · rcases p0_3 (m.d 0 2) (by simp) with h714 | h714
      · rcases p0_3 (m.d 0 3) (by simp) with h715 | h715
        · linarith only [h715, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h717 | h717
          · rcases p0_3 (m.d 0 5) (by simp) with h718 | h718
            · rcases m.htr 0 1 2 (by decide) (by decide) with h719 | h719
              · rcases m.htr 0 1 3 (by decide) (by decide) with h720 | h720
                · rcases m.htr 0 1 4 (by decide) (by decide) with h721 | h721
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h722 | h722
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h723 | h723
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h724 | h724
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h725 | h725
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h726 | h726
                            · linarith only [h717, h719, h724, h726, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                            · linarith only [h717, h726, hc03, hc34, hlam, hphi, p0_1]
                          · linarith only [h714, h725, hlam]
                        · linarith only [h714, h720, h724, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h714, h720, h723, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h713, h722, hlam]
                  · linarith only [h713, h720, h721, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h714, h719, h720, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h719, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h718, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h737 | h737
            · rcases m.htr 0 1 2 (by decide) (by decide) with h738 | h738
              · rcases m.htr 0 1 3 (by decide) (by decide) with h739 | h739
                · rcases m.htr 0 1 4 (by decide) (by decide) with h740 | h740
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h741 | h741
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h742 | h742
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h743 | h743
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h744 | h744
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h745 | h745
                            · linarith only [h738, h744, h745, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                            · linarith only [h717, h745, hlam]
                          · linarith only [h714, h744, hlam]
                        · linarith only [h714, h743, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h714, h739, h742, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h713, h741, hlam]
                  · linarith only [h713, h739, h740, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h714, h738, h739, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h738, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h737, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h756 | h756
        · linarith only [h756, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h758 | h758
          · rcases p0_3 (m.d 0 5) (by simp) with h759 | h759
            · rcases m.htr 0 1 2 (by decide) (by decide) with h760 | h760
              · rcases m.htr 0 1 3 (by decide) (by decide) with h761 | h761
                · rcases m.htr 0 1 4 (by decide) (by decide) with h762 | h762
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h763 | h763
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h764 | h764
                      · linarith only [h714, h764, hlam]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h766 | h766
                        · linarith only [h758, h762, h764, h766, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                        · linarith only [h758, h764, h766, hc02, hc24, hlam, hphi, p0_1]
                    · linarith only [h713, h763, hlam]
                  · linarith only [h713, h714, h760, h762, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h713, h714, h760, h761, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h714, h760, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h759, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h774 | h774
            · rcases m.htr 0 1 2 (by decide) (by decide) with h775 | h775
              · rcases m.htr 0 1 3 (by decide) (by decide) with h776 | h776
                · rcases m.htr 0 1 4 (by decide) (by decide) with h777 | h777
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h778 | h778
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h779 | h779
                      · linarith only [h714, h779, hlam]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h781 | h781
                        · linarith only [h778, h779, h781, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h783 | h783
                          · linarith only [h778, h779, h783, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                          · linarith only [h779, h783, hc02, hc25, hlam, hphi, p0_1]
                    · linarith only [h713, h778, hlam]
                  · linarith only [h713, h777, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h713, h714, h775, h776, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h714, h775, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h774, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h791 | h791
      · rcases p0_3 (m.d 0 3) (by simp) with h792 | h792
        · linarith only [h792, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h794 | h794
          · rcases p0_3 (m.d 0 5) (by simp) with h795 | h795
            · rcases m.htr 0 1 2 (by decide) (by decide) with h796 | h796
              · linarith only [h713, h791, h796, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h791, h796, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h795, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h800 | h800
            · rcases m.htr 0 1 2 (by decide) (by decide) with h801 | h801
              · linarith only [h713, h791, h801, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h713, h791, h801, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h800, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h805 | h805
        · linarith only [h805, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h807 | h807
          · rcases p0_3 (m.d 0 5) (by simp) with h808 | h808
            · rcases m.htr 0 1 2 (by decide) (by decide) with h809 | h809
              · linarith only [h713, h807, h809, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h811 | h811
                · linarith only [h713, h811, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h813 | h813
                  · linarith only [h791, h807, h809, h813, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h791, h807, h809, h813, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h808, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h817 | h817
            · rcases m.htr 0 1 2 (by decide) (by decide) with h818 | h818
              · linarith only [h713, h818, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h820 | h820
                · linarith only [h713, h820, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h822 | h822
                  · linarith only [h791, h818, h822, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h824 | h824
                    · linarith only [h791, h818, h824, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                    · linarith only [h791, h818, h824, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h817, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h828 | h828
    · rcases p0_3 (m.d 0 2) (by simp) with h829 | h829
      · rcases p0_3 (m.d 0 3) (by simp) with h830 | h830
        · rcases p0_3 (m.d 0 4) (by simp) with h831 | h831
          · linarith only [h831, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h833 | h833
            · rcases m.htr 0 1 2 (by decide) (by decide) with h834 | h834
              · rcases m.htr 0 1 3 (by decide) (by decide) with h835 | h835
                · rcases m.htr 0 1 4 (by decide) (by decide) with h836 | h836
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h837 | h837
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h838 | h838
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h839 | h839
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h840 | h840
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h841 | h841
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h842 | h842
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h843 | h843
                                · linarith only [h843, hlam, p0_0]
                                · linarith only [h836, h843, hc14, hc45, hlam, hphi, p0_1]
                              · linarith only [h830, h842, hlam]
                            · linarith only [h830, h836, h841, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                          · linarith only [h829, h840, hlam]
                        · linarith only [h830, h836, h838, h839, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                      · linarith only [h829, h836, h838, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h828, h837, hlam]
                  · linarith only [h828, h836, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h829, h834, h835, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h828, h834, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h833, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h856 | h856
          · linarith only [h856, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h858 | h858
            · rcases m.htr 0 1 2 (by decide) (by decide) with h859 | h859
              · rcases m.htr 0 1 3 (by decide) (by decide) with h860 | h860
                · rcases m.htr 0 1 4 (by decide) (by decide) with h861 | h861
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h862 | h862
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h863 | h863
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h864 | h864
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h865 | h865
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h866 | h866
                            · linarith only [h830, h866, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h868 | h868
                              · linarith only [h859, h865, h866, h868, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                              · linarith only [h866, h868, hc03, hc35, hlam, hphi, p0_1]
                          · linarith only [h829, h865, hlam]
                        · linarith only [h829, h864, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                      · linarith only [h829, h830, h860, h863, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h828, h862, hlam]
                  · linarith only [h828, h830, h860, h861, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h829, h830, h859, h860, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h828, h830, h859, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h858, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h879 | h879
        · rcases p0_3 (m.d 0 4) (by simp) with h880 | h880
          · linarith only [h880, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h882 | h882
            · rcases m.htr 0 1 2 (by decide) (by decide) with h883 | h883
              · rcases m.htr 0 1 3 (by decide) (by decide) with h884 | h884
                · rcases m.htr 0 1 4 (by decide) (by decide) with h885 | h885
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h886 | h886
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h887 | h887
                      · linarith only [h829, h879, h884, h887, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h829, h879, h887, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h828, h886, hlam]
                  · linarith only [h829, h879, h883, h884, h885, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h828, h829, h883, h884, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h828, h829, h883, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h882, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h895 | h895
          · linarith only [h895, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h897 | h897
            · rcases m.htr 0 1 2 (by decide) (by decide) with h898 | h898
              · rcases m.htr 0 1 3 (by decide) (by decide) with h899 | h899
                · rcases m.htr 0 1 4 (by decide) (by decide) with h900 | h900
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h901 | h901
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h902 | h902
                      · linarith only [h829, h901, h902, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h904 | h904
                        · linarith only [h829, h904, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h906 | h906
                          · linarith only [h879, h901, h902, h906, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                          · linarith only [h879, h902, h906, hc02, hc25, hlam, hphi, p0_1]
                    · linarith only [h828, h901, hlam]
                  · linarith only [h828, h829, h898, h900, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h828, h829, h898, h899, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h828, h829, h898, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h897, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h914 | h914
      · rcases p0_3 (m.d 0 3) (by simp) with h915 | h915
        · rcases p0_3 (m.d 0 4) (by simp) with h916 | h916
          · linarith only [h916, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h918 | h918
            · rcases m.htr 0 1 2 (by decide) (by decide) with h919 | h919
              · linarith only [h828, h914, h919, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h828, h914, h919, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h918, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h923 | h923
          · linarith only [h923, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h925 | h925
            · rcases m.htr 0 1 2 (by decide) (by decide) with h926 | h926
              · linarith only [h828, h914, h926, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h828, h914, h926, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h925, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h930 | h930
        · rcases p0_3 (m.d 0 4) (by simp) with h931 | h931
          · linarith only [h931, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h933 | h933
            · rcases m.htr 0 1 2 (by decide) (by decide) with h934 | h934
              · linarith only [h828, h930, h934, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h936 | h936
                · linarith only [h914, h930, h934, h936, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h914, h930, h934, h936, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h933, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h940 | h940
          · linarith only [h940, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h942 | h942
            · rcases m.htr 0 1 2 (by decide) (by decide) with h943 | h943
              · linarith only [h828, h943, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h945 | h945
                · linarith only [h914, h943, h945, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h947 | h947
                  · linarith only [h828, h947, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h949 | h949
                    · linarith only [h914, h943, h949, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                    · linarith only [h914, h943, h949, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h942, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_H_L_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h6 | h6
    · linarith only [h6, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h8 | h8
      · rcases p0_3 (m.d 2 5) (by simp) with h9 | h9
        · rcases p0_3 (m.d 3 5) (by simp) with h10 | h10
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · rcases m.htr 0 1 4 (by decide) (by decide) with h12 | h12
              · rcases m.htr 0 1 5 (by decide) (by decide) with h13 | h13
                · linarith only [h13, hlam, p0_0]
                · linarith only [h11, h13, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h16 | h16
                · linarith only [h16, hlam, p0_0]
                · linarith only [h11, h16, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h19 | h19
              · rcases m.htr 0 1 5 (by decide) (by decide) with h20 | h20
                · linarith only [h20, hlam, p0_0]
                · linarith only [h19, h20, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h23 | h23
                · linarith only [h23, hlam, p0_0]
                · linarith only [h10, h23, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · rcases m.htr 0 1 4 (by decide) (by decide) with h27 | h27
              · rcases m.htr 0 1 5 (by decide) (by decide) with h28 | h28
                · linarith only [h28, hlam, p0_0]
                · linarith only [h26, h28, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h31 | h31
                · linarith only [h31, hlam, p0_0]
                · linarith only [h26, h31, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h34 | h34
              · rcases m.htr 0 1 5 (by decide) (by decide) with h35 | h35
                · linarith only [h35, hlam, p0_0]
                · linarith only [h34, h35, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h38 | h38
                · linarith only [h38, hlam, p0_0]
                · linarith only [h38, h9, hc01, hc25, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h41 | h41
          · rcases p0_3 (m.d 4 5) (by simp) with h42 | h42
            · rcases m.htr 0 1 4 (by decide) (by decide) with h43 | h43
              · rcases m.htr 0 1 5 (by decide) (by decide) with h44 | h44
                · linarith only [h44, hlam, p0_0]
                · linarith only [h42, h44, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h47 | h47
                · linarith only [h47, hlam, p0_0]
                · linarith only [h42, h47, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h50 | h50
              · rcases m.htr 0 1 5 (by decide) (by decide) with h51 | h51
                · linarith only [h51, hlam, p0_0]
                · linarith only [h50, h51, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h54 | h54
                · linarith only [h54, hlam, p0_0]
                · linarith only [h41, h54, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h57 | h57
            · rcases m.htr 0 1 4 (by decide) (by decide) with h58 | h58
              · rcases m.htr 0 1 5 (by decide) (by decide) with h59 | h59
                · linarith only [h59, hlam, p0_0]
                · linarith only [h57, h58, h59, hc14, hc45, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h62 | h62
                · linarith only [h62, hlam, p0_0]
                · linarith only [h57, h62, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h65 | h65
              · rcases m.htr 0 1 5 (by decide) (by decide) with h66 | h66
                · linarith only [h66, hlam, p0_0]
                · linarith only [h65, h66, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h69 | h69
                · linarith only [h69, hlam, p0_0]
                · linarith only [h69, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h8, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h74 | h74
    · linarith only [h74, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h76 | h76
      · rcases p0_3 (m.d 2 5) (by simp) with h77 | h77
        · linarith only [h77, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h79 | h79
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · rcases m.htr 0 1 4 (by decide) (by decide) with h81 | h81
              · rcases m.htr 0 1 5 (by decide) (by decide) with h82 | h82
                · linarith only [h82, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h74, h81, h82, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h85 | h85
                · linarith only [h74, h81, h85, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                · linarith only [h74, h85, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h88 | h88
              · rcases m.htr 0 1 5 (by decide) (by decide) with h89 | h89
                · linarith only [h74, h89, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h74, h88, h89, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h92 | h92
                · linarith only [h74, h88, h92, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                · linarith only [h74, h92, hc01, hc15, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h95 | h95
            · rcases m.htr 0 1 4 (by decide) (by decide) with h96 | h96
              · rcases m.htr 0 1 5 (by decide) (by decide) with h97 | h97
                · linarith only [h74, h97, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h74, h96, h97, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h100 | h100
                · linarith only [h100, h74, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h100, h74, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h103 | h103
              · rcases m.htr 0 1 5 (by decide) (by decide) with h104 | h104
                · linarith only [h104, h74, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h103, h104, h74, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h107 | h107
                · linarith only [h103, h107, h74, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                · linarith only [h107, h74, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h76, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h111 | h111
    · linarith only [h111, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h113 | h113
      · rcases p0_3 (m.d 2 5) (by simp) with h114 | h114
        · rcases p0_3 (m.d 3 5) (by simp) with h115 | h115
          · linarith only [h115, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h117 | h117
            · rcases m.htr 0 1 4 (by decide) (by decide) with h118 | h118
              · rcases m.htr 0 1 5 (by decide) (by decide) with h119 | h119
                · linarith only [h119, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h111, h118, h119, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h122 | h122
                · linarith only [h111, h118, h122, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                · linarith only [h111, h122, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h125 | h125
              · rcases m.htr 0 1 5 (by decide) (by decide) with h126 | h126
                · linarith only [h111, h126, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h111, h125, h126, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h129 | h129
                · linarith only [h111, h125, h129, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                · linarith only [h111, h129, hc01, hc15, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h134 | h134
            · rcases m.htr 0 1 4 (by decide) (by decide) with h135 | h135
              · rcases m.htr 0 1 5 (by decide) (by decide) with h136 | h136
                · linarith only [h111, h136, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h111, h136, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h139 | h139
                · linarith only [h111, h135, h139, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                · linarith only [h111, h139, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h142 | h142
              · rcases m.htr 0 1 5 (by decide) (by decide) with h143 | h143
                · linarith only [h111, h143, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h111, h142, h143, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h146 | h146
                · linarith only [h111, h146, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h111, h146, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h113, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h150 | h150
    · linarith only [h150, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h152 | h152
      · rcases p0_3 (m.d 2 5) (by simp) with h153 | h153
        · rcases p0_3 (m.d 3 5) (by simp) with h154 | h154
          · rcases p0_3 (m.d 4 5) (by simp) with h155 | h155
            · linarith only [h155, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h157 | h157
              · rcases m.htr 0 1 5 (by decide) (by decide) with h158 | h158
                · linarith only [h158, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h150, h158, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h161 | h161
                · linarith only [h150, h157, h161, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                · linarith only [h150, h161, hc01, hc15, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h164 | h164
            · linarith only [h164, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h166 | h166
              · rcases m.htr 0 1 5 (by decide) (by decide) with h167 | h167
                · linarith only [h150, h167, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h150, h166, h167, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h170 | h170
                · linarith only [h150, h166, h170, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                · linarith only [h150, h170, hc01, hc15, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h173 | h173
          · rcases p0_3 (m.d 4 5) (by simp) with h174 | h174
            · linarith only [h174, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h176 | h176
              · rcases m.htr 0 1 5 (by decide) (by decide) with h177 | h177
                · linarith only [h150, h177, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h150, h176, h177, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h180 | h180
                · linarith only [h150, h176, h180, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                · linarith only [h150, h180, hc01, hc15, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h183 | h183
            · linarith only [h183, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h185 | h185
              · rcases m.htr 0 1 5 (by decide) (by decide) with h186 | h186
                · linarith only [h150, h186, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h150, h186, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h189 | h189
                · linarith only [h150, h185, h189, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                · linarith only [h150, h189, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h152, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h193 | h193
    · linarith only [h193, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h195 | h195
      · rcases p0_3 (m.d 2 5) (by simp) with h196 | h196
        · rcases p0_3 (m.d 3 5) (by simp) with h197 | h197
          · rcases p0_3 (m.d 4 5) (by simp) with h198 | h198
            · rcases m.htr 0 1 4 (by decide) (by decide) with h199 | h199
              · rcases m.htr 0 1 5 (by decide) (by decide) with h200 | h200
                · linarith only [h195, h200, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h195, h199, h200, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h203 | h203
                · linarith only [h195, h203, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h195, h203, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h206 | h206
              · rcases m.htr 0 1 5 (by decide) (by decide) with h207 | h207
                · linarith only [h195, h207, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h195, h206, h207, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h210 | h210
                · linarith only [h195, h210, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h195, h210, hc01, hc15, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h213 | h213
            · rcases m.htr 0 1 4 (by decide) (by decide) with h214 | h214
              · rcases m.htr 0 1 5 (by decide) (by decide) with h215 | h215
                · linarith only [h195, h215, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h195, h214, h215, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h218 | h218
                · linarith only [h195, h218, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h195, h218, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h221 | h221
              · rcases m.htr 0 1 5 (by decide) (by decide) with h222 | h222
                · linarith only [h195, h222, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h195, h221, h222, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h225 | h225
                · linarith only [h195, h225, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h195, h225, hc01, hc15, hlam, hphi, p0_1]
        · linarith only [h196, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h229 | h229
        · rcases p0_3 (m.d 3 5) (by simp) with h230 | h230
          · rcases p0_3 (m.d 4 5) (by simp) with h231 | h231
            · rcases m.htr 0 1 4 (by decide) (by decide) with h232 | h232
              · rcases m.htr 0 1 5 (by decide) (by decide) with h233 | h233
                · rcases m.htr 0 2 5 (by decide) (by decide) with h234 | h234
                  · linarith only [h234, hlam, p0_0]
                  · linarith only [h231, h234, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h195, h233, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h238 | h238
                · rcases m.htr 0 2 5 (by decide) (by decide) with h239 | h239
                  · linarith only [h239, hlam, p0_0]
                  · linarith only [h231, h239, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h195, h238, hlam]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h243 | h243
              · rcases m.htr 0 1 5 (by decide) (by decide) with h244 | h244
                · rcases m.htr 0 2 5 (by decide) (by decide) with h245 | h245
                  · linarith only [h245, hlam, p0_0]
                  · linarith only [h245, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h195, h244, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h249 | h249
                · rcases m.htr 0 2 5 (by decide) (by decide) with h250 | h250
                  · linarith only [h250, hlam, p0_0]
                  · linarith only [h230, h250, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h195, h249, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h254 | h254
            · rcases m.htr 0 1 4 (by decide) (by decide) with h255 | h255
              · rcases m.htr 0 1 5 (by decide) (by decide) with h256 | h256
                · rcases m.htr 0 2 5 (by decide) (by decide) with h257 | h257
                  · linarith only [h257, hlam, p0_0]
                  · linarith only [h254, h257, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h195, h256, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h261 | h261
                · rcases m.htr 0 2 5 (by decide) (by decide) with h262 | h262
                  · linarith only [h262, hlam, p0_0]
                  · linarith only [h254, h262, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h195, h261, hlam]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h266 | h266
              · rcases m.htr 0 1 5 (by decide) (by decide) with h267 | h267
                · rcases m.htr 0 2 5 (by decide) (by decide) with h268 | h268
                  · linarith only [h268, hlam, p0_0]
                  · linarith only [h268, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h195, h267, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h272 | h272
                · rcases m.htr 0 2 5 (by decide) (by decide) with h273 | h273
                  · linarith only [h273, hlam, p0_0]
                  · linarith only [h273, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h195, h272, hlam]
        · linarith only [h229, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h278 | h278
    · linarith only [h278, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h280 | h280
      · linarith only [h280, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h282 | h282
        · rcases p0_3 (m.d 3 5) (by simp) with h283 | h283
          · rcases p0_3 (m.d 4 5) (by simp) with h284 | h284
            · rcases m.htr 0 1 4 (by decide) (by decide) with h285 | h285
              · rcases m.htr 0 1 5 (by decide) (by decide) with h286 | h286
                · linarith only [h278, h286, hlam]
                · linarith only [h284, h286, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h289 | h289
                · linarith only [h278, h289, hlam]
                · linarith only [h284, h289, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h292 | h292
              · rcases m.htr 0 1 5 (by decide) (by decide) with h293 | h293
                · linarith only [h278, h293, hlam]
                · linarith only [h293, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h296 | h296
                · linarith only [h278, h296, hlam]
                · linarith only [h283, h296, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h299 | h299
            · rcases m.htr 0 1 4 (by decide) (by decide) with h300 | h300
              · rcases m.htr 0 1 5 (by decide) (by decide) with h301 | h301
                · linarith only [h278, h301, hlam]
                · linarith only [h299, h301, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h304 | h304
                · linarith only [h278, h304, hlam]
                · linarith only [h299, h304, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h307 | h307
              · rcases m.htr 0 1 5 (by decide) (by decide) with h308 | h308
                · linarith only [h278, h308, hlam]
                · linarith only [h307, h308, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h311 | h311
                · linarith only [h278, h311, hlam]
                · linarith only [h311, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h282, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h316 | h316
    · linarith only [h316, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h318 | h318
      · rcases p0_3 (m.d 2 5) (by simp) with h319 | h319
        · rcases p0_3 (m.d 3 5) (by simp) with h320 | h320
          · linarith only [h320, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h322 | h322
            · rcases m.htr 0 1 4 (by decide) (by decide) with h323 | h323
              · rcases m.htr 0 1 5 (by decide) (by decide) with h324 | h324
                · linarith only [h318, h324, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h316, h318, h323, h324, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h327 | h327
                · linarith only [h316, h318, h327, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h316, h318, h327, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h330 | h330
              · rcases m.htr 0 1 5 (by decide) (by decide) with h331 | h331
                · linarith only [h316, h318, h331, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h316, h318, h330, h331, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h334 | h334
                · linarith only [h316, h318, h334, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h316, h318, h334, hc01, hc15, hlam, hphi, p0_1]
        · linarith only [h319, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h338 | h338
        · rcases p0_3 (m.d 3 5) (by simp) with h339 | h339
          · linarith only [h339, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h341 | h341
            · rcases m.htr 0 1 4 (by decide) (by decide) with h342 | h342
              · rcases m.htr 0 1 5 (by decide) (by decide) with h343 | h343
                · rcases m.htr 0 2 5 (by decide) (by decide) with h344 | h344
                  · linarith only [h316, h343, h344, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h316, h341, h344, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h318, h341, h342, h343, hc14, hc45, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h348 | h348
                · rcases m.htr 0 2 5 (by decide) (by decide) with h349 | h349
                  · linarith only [h316, h348, h349, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h316, h341, h349, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h318, h341, h348, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h353 | h353
              · rcases m.htr 0 1 5 (by decide) (by decide) with h354 | h354
                · rcases m.htr 0 2 5 (by decide) (by decide) with h355 | h355
                  · linarith only [h316, h355, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h316, h355, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h318, h353, h354, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h359 | h359
                · rcases m.htr 0 2 5 (by decide) (by decide) with h360 | h360
                  · linarith only [h316, h360, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h316, h360, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h318, h359, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h338, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h365 | h365
    · linarith only [h365, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h367 | h367
      · rcases p0_3 (m.d 2 5) (by simp) with h368 | h368
        · rcases p0_3 (m.d 3 5) (by simp) with h369 | h369
          · rcases p0_3 (m.d 4 5) (by simp) with h370 | h370
            · linarith only [h370, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h372 | h372
              · rcases m.htr 0 1 5 (by decide) (by decide) with h373 | h373
                · linarith only [h367, h373, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h365, h367, h373, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h376 | h376
                · linarith only [h365, h367, h372, h376, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                · linarith only [h365, h367, h376, hc01, hc15, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h379 | h379
            · linarith only [h379, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h381 | h381
              · rcases m.htr 0 1 5 (by decide) (by decide) with h382 | h382
                · linarith only [h365, h367, h382, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h365, h367, h381, h382, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h385 | h385
                · linarith only [h365, h367, h385, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h365, h367, h385, hc01, hc15, hlam, hphi, p0_1]
        · linarith only [h368, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h389 | h389
        · rcases p0_3 (m.d 3 5) (by simp) with h390 | h390
          · rcases p0_3 (m.d 4 5) (by simp) with h391 | h391
            · linarith only [h391, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h393 | h393
              · rcases m.htr 0 1 5 (by decide) (by decide) with h394 | h394
                · rcases m.htr 0 2 5 (by decide) (by decide) with h395 | h395
                  · linarith only [h365, h395, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h365, h395, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h367, h390, h394, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h399 | h399
                · rcases m.htr 0 2 5 (by decide) (by decide) with h400 | h400
                  · linarith only [h365, h400, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h365, h400, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h367, h390, h399, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h404 | h404
            · linarith only [h404, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h406 | h406
              · rcases m.htr 0 1 5 (by decide) (by decide) with h407 | h407
                · rcases m.htr 0 2 5 (by decide) (by decide) with h408 | h408
                  · linarith only [h365, h408, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h365, h408, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h367, h406, h407, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h412 | h412
                · rcases m.htr 0 2 5 (by decide) (by decide) with h413 | h413
                  · linarith only [h365, h413, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h365, h413, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h367, h412, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h389, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h418 | h418
    · linarith only [h418, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h420 | h420
      · rcases p0_3 (m.d 2 5) (by simp) with h421 | h421
        · rcases p0_3 (m.d 3 5) (by simp) with h422 | h422
          · rcases p0_3 (m.d 4 5) (by simp) with h423 | h423
            · rcases m.htr 0 1 4 (by decide) (by decide) with h424 | h424
              · rcases m.htr 0 1 5 (by decide) (by decide) with h425 | h425
                · linarith only [h420, h425, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h420, h425, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h428 | h428
                · linarith only [h420, h428, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h420, h428, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h431 | h431
              · rcases m.htr 0 1 5 (by decide) (by decide) with h432 | h432
                · linarith only [h420, h432, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h420, h432, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h435 | h435
                · linarith only [h420, h435, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h420, h435, hc01, hc15, hlam, hphi, p0_1]
          · linarith only [h422, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h439 | h439
          · rcases p0_3 (m.d 4 5) (by simp) with h440 | h440
            · rcases m.htr 0 1 4 (by decide) (by decide) with h441 | h441
              · rcases m.htr 0 1 5 (by decide) (by decide) with h442 | h442
                · linarith only [h420, h442, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h420, h442, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h445 | h445
                · linarith only [h420, h441, h445, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                · linarith only [h420, h445, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h448 | h448
              · rcases m.htr 0 1 5 (by decide) (by decide) with h449 | h449
                · linarith only [h420, h449, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h420, h448, h449, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h452 | h452
                · linarith only [h420, h452, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h420, h452, hc01, hc15, hlam, hphi, p0_1]
          · linarith only [h439, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h456 | h456
        · rcases p0_3 (m.d 3 5) (by simp) with h457 | h457
          · rcases p0_3 (m.d 4 5) (by simp) with h458 | h458
            · rcases m.htr 0 1 4 (by decide) (by decide) with h459 | h459
              · rcases m.htr 0 1 5 (by decide) (by decide) with h460 | h460
                · rcases m.htr 0 2 5 (by decide) (by decide) with h461 | h461
                  · linarith only [h456, h460, h461, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h458, h461, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h420, h460, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h465 | h465
                · rcases m.htr 0 2 5 (by decide) (by decide) with h466 | h466
                  · linarith only [h456, h465, h466, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h458, h466, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h420, h465, hlam]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h470 | h470
              · rcases m.htr 0 1 5 (by decide) (by decide) with h471 | h471
                · rcases m.htr 0 2 5 (by decide) (by decide) with h472 | h472
                  · linarith only [h456, h471, h472, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h456, h472, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h420, h471, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h476 | h476
                · rcases m.htr 0 2 5 (by decide) (by decide) with h477 | h477
                  · linarith only [h456, h477, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h456, h477, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h420, h476, hlam]
          · linarith only [h457, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h482 | h482
          · rcases p0_3 (m.d 4 5) (by simp) with h483 | h483
            · rcases m.htr 0 1 4 (by decide) (by decide) with h484 | h484
              · rcases m.htr 0 1 5 (by decide) (by decide) with h485 | h485
                · rcases m.htr 0 2 5 (by decide) (by decide) with h486 | h486
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h487 | h487
                    · linarith only [h487, hlam, p0_0]
                    · linarith only [h483, h487, hc03, hc45, hlam, hphi, ht34, p0_1]
                  · linarith only [h456, h486, hlam]
                · linarith only [h420, h485, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h492 | h492
                · rcases m.htr 0 2 5 (by decide) (by decide) with h493 | h493
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h494 | h494
                    · linarith only [h494, hlam, p0_0]
                    · linarith only [h483, h494, hc03, hc45, hlam, hphi, ht34, p0_1]
                  · linarith only [h456, h493, hlam]
                · linarith only [h420, h492, hlam]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h499 | h499
              · rcases m.htr 0 1 5 (by decide) (by decide) with h500 | h500
                · rcases m.htr 0 2 5 (by decide) (by decide) with h501 | h501
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h502 | h502
                    · linarith only [h502, hlam, p0_0]
                    · linarith only [h502, hc03, hc35, hlam, hphi, p0_1]
                  · linarith only [h456, h501, hlam]
                · linarith only [h420, h500, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h507 | h507
                · rcases m.htr 0 2 5 (by decide) (by decide) with h508 | h508
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h509 | h509
                    · linarith only [h509, hlam, p0_0]
                    · linarith only [h509, hc03, hc35, hlam, hphi, p0_1]
                  · linarith only [h456, h508, hlam]
                · linarith only [h420, h507, hlam]
          · linarith only [h482, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h515 | h515
    · linarith only [h515, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h517 | h517
      · linarith only [h517, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h519 | h519
        · rcases p0_3 (m.d 3 5) (by simp) with h520 | h520
          · rcases p0_3 (m.d 4 5) (by simp) with h521 | h521
            · rcases m.htr 0 1 4 (by decide) (by decide) with h522 | h522
              · rcases m.htr 0 1 5 (by decide) (by decide) with h523 | h523
                · linarith only [h515, h523, hlam]
                · linarith only [h521, h523, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h526 | h526
                · linarith only [h515, h526, hlam]
                · linarith only [h521, h526, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h529 | h529
              · rcases m.htr 0 1 5 (by decide) (by decide) with h530 | h530
                · linarith only [h515, h530, hlam]
                · linarith only [h519, h529, h530, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h533 | h533
                · linarith only [h515, h533, hlam]
                · linarith only [h533, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h520, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h537 | h537
          · rcases p0_3 (m.d 4 5) (by simp) with h538 | h538
            · rcases m.htr 0 1 4 (by decide) (by decide) with h539 | h539
              · rcases m.htr 0 1 5 (by decide) (by decide) with h540 | h540
                · linarith only [h515, h540, hlam]
                · linarith only [h538, h539, h540, hc14, hc45, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h543 | h543
                · linarith only [h515, h543, hlam]
                · linarith only [h538, h543, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h546 | h546
              · rcases m.htr 0 1 5 (by decide) (by decide) with h547 | h547
                · linarith only [h515, h547, hlam]
                · linarith only [h546, h547, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h550 | h550
                · linarith only [h515, h550, hlam]
                · linarith only [h550, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h537, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h554 | h554
    · linarith only [h554, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h556 | h556
      · rcases p0_3 (m.d 2 5) (by simp) with h557 | h557
        · linarith only [h557, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h559 | h559
          · rcases p0_3 (m.d 4 5) (by simp) with h560 | h560
            · rcases m.htr 0 1 4 (by decide) (by decide) with h561 | h561
              · rcases m.htr 0 1 5 (by decide) (by decide) with h562 | h562
                · linarith only [h556, h562, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h554, h556, h562, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h565 | h565
                · linarith only [h554, h556, h565, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h554, h556, h565, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h568 | h568
              · rcases m.htr 0 1 5 (by decide) (by decide) with h569 | h569
                · linarith only [h554, h556, h569, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h554, h556, h568, h569, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h572 | h572
                · linarith only [h554, h556, h572, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h554, h556, h572, hc01, hc15, hlam, hphi, p0_1]
          · linarith only [h559, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h576 | h576
        · linarith only [h576, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h578 | h578
          · rcases p0_3 (m.d 4 5) (by simp) with h579 | h579
            · rcases m.htr 0 1 4 (by decide) (by decide) with h580 | h580
              · rcases m.htr 0 1 5 (by decide) (by decide) with h581 | h581
                · rcases m.htr 0 2 5 (by decide) (by decide) with h582 | h582
                  · linarith only [h554, h582, hlam]
                  · linarith only [h579, h582, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h556, h579, h581, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h586 | h586
                · rcases m.htr 0 2 5 (by decide) (by decide) with h587 | h587
                  · linarith only [h554, h587, hlam]
                  · linarith only [h579, h587, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h556, h579, h586, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h591 | h591
              · rcases m.htr 0 1 5 (by decide) (by decide) with h592 | h592
                · rcases m.htr 0 2 5 (by decide) (by decide) with h593 | h593
                  · linarith only [h554, h593, hlam]
                  · linarith only [h593, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h556, h591, h592, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h597 | h597
                · rcases m.htr 0 2 5 (by decide) (by decide) with h598 | h598
                  · linarith only [h554, h598, hlam]
                  · linarith only [h598, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h556, h597, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h578, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h604 | h604
    · linarith only [h604, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h606 | h606
      · rcases p0_3 (m.d 2 5) (by simp) with h607 | h607
        · rcases p0_3 (m.d 3 5) (by simp) with h608 | h608
          · rcases p0_3 (m.d 4 5) (by simp) with h609 | h609
            · linarith only [h609, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h611 | h611
              · rcases m.htr 0 1 5 (by decide) (by decide) with h612 | h612
                · linarith only [h606, h612, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h604, h606, h612, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h615 | h615
                · linarith only [h604, h606, h615, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h604, h606, h615, hc01, hc15, hlam, hphi, p0_1]
          · linarith only [h608, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h619 | h619
          · rcases p0_3 (m.d 4 5) (by simp) with h620 | h620
            · linarith only [h620, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h622 | h622
              · rcases m.htr 0 1 5 (by decide) (by decide) with h623 | h623
                · linarith only [h604, h606, h623, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h604, h606, h623, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h626 | h626
                · linarith only [h604, h606, h622, h626, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                · linarith only [h604, h606, h626, hc01, hc15, hlam, hphi, p0_1]
          · linarith only [h619, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h630 | h630
        · rcases p0_3 (m.d 3 5) (by simp) with h631 | h631
          · rcases p0_3 (m.d 4 5) (by simp) with h632 | h632
            · linarith only [h632, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h634 | h634
              · rcases m.htr 0 1 5 (by decide) (by decide) with h635 | h635
                · rcases m.htr 0 2 5 (by decide) (by decide) with h636 | h636
                  · linarith only [h604, h630, h636, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h604, h630, h636, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h606, h634, h635, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h640 | h640
                · rcases m.htr 0 2 5 (by decide) (by decide) with h641 | h641
                  · linarith only [h604, h630, h641, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h604, h630, h641, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h606, h640, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h631, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h646 | h646
          · rcases p0_3 (m.d 4 5) (by simp) with h647 | h647
            · linarith only [h647, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h649 | h649
              · rcases m.htr 0 1 5 (by decide) (by decide) with h650 | h650
                · rcases m.htr 0 2 5 (by decide) (by decide) with h651 | h651
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h652 | h652
                    · linarith only [h604, h652, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                    · linarith only [h604, h652, hc03, hc35, hlam, hphi, p0_1]
                  · linarith only [h630, h651, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h606, h650, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h657 | h657
                · rcases m.htr 0 2 5 (by decide) (by decide) with h658 | h658
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h659 | h659
                    · linarith only [h604, h659, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                    · linarith only [h604, h659, hc03, hc35, hlam, hphi, p0_1]
                  · linarith only [h630, h658, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h606, h657, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h646, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h665 | h665
    · linarith only [h665, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h667 | h667
      · rcases p0_3 (m.d 2 5) (by simp) with h668 | h668
        · rcases p0_3 (m.d 3 5) (by simp) with h669 | h669
          · rcases p0_3 (m.d 4 5) (by simp) with h670 | h670
            · rcases m.htr 0 1 4 (by decide) (by decide) with h671 | h671
              · rcases m.htr 0 1 5 (by decide) (by decide) with h672 | h672
                · linarith only [h667, h672, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h667, h672, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h675 | h675
                · linarith only [h667, h675, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h667, h675, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h670, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h679 | h679
            · rcases m.htr 0 1 4 (by decide) (by decide) with h680 | h680
              · rcases m.htr 0 1 5 (by decide) (by decide) with h681 | h681
                · linarith only [h667, h681, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h667, h680, h681, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h684 | h684
                · linarith only [h667, h684, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h667, h684, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h679, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h688 | h688
          · rcases p0_3 (m.d 4 5) (by simp) with h689 | h689
            · rcases m.htr 0 1 4 (by decide) (by decide) with h690 | h690
              · rcases m.htr 0 1 5 (by decide) (by decide) with h691 | h691
                · linarith only [h667, h691, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h667, h690, h691, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h694 | h694
                · linarith only [h667, h690, h694, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                · linarith only [h667, h694, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h689, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h698 | h698
            · rcases m.htr 0 1 4 (by decide) (by decide) with h699 | h699
              · rcases m.htr 0 1 5 (by decide) (by decide) with h700 | h700
                · linarith only [h667, h700, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h667, h699, h700, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h703 | h703
                · linarith only [h667, h703, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h667, h703, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h698, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h707 | h707
        · rcases p0_3 (m.d 3 5) (by simp) with h708 | h708
          · rcases p0_3 (m.d 4 5) (by simp) with h709 | h709
            · rcases m.htr 0 1 4 (by decide) (by decide) with h710 | h710
              · rcases m.htr 0 1 5 (by decide) (by decide) with h711 | h711
                · rcases m.htr 0 2 5 (by decide) (by decide) with h712 | h712
                  · linarith only [h707, h711, h712, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h712, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h667, h711, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h716 | h716
                · rcases m.htr 0 2 5 (by decide) (by decide) with h717 | h717
                  · linarith only [h707, h716, h717, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h717, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h667, h716, hlam]
            · linarith only [h709, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h722 | h722
            · rcases m.htr 0 1 4 (by decide) (by decide) with h723 | h723
              · rcases m.htr 0 1 5 (by decide) (by decide) with h724 | h724
                · rcases m.htr 0 2 5 (by decide) (by decide) with h725 | h725
                  · linarith only [h707, h724, h725, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h725, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h667, h724, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h729 | h729
                · rcases m.htr 0 2 5 (by decide) (by decide) with h730 | h730
                  · linarith only [h707, h729, h730, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h730, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h667, h729, hlam]
            · linarith only [h722, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h735 | h735
          · rcases p0_3 (m.d 4 5) (by simp) with h736 | h736
            · rcases m.htr 0 1 4 (by decide) (by decide) with h737 | h737
              · rcases m.htr 0 1 5 (by decide) (by decide) with h738 | h738
                · rcases m.htr 0 2 5 (by decide) (by decide) with h739 | h739
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h740 | h740
                    · linarith only [h735, h738, h740, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                    · linarith only [h740, hc03, hc45, hlam, hphi, ht34, p0_1]
                  · linarith only [h707, h739, hlam]
                · linarith only [h667, h738, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h745 | h745
                · rcases m.htr 0 2 5 (by decide) (by decide) with h746 | h746
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h747 | h747
                    · linarith only [h735, h745, h747, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                    · linarith only [h747, hc03, hc45, hlam, hphi, ht34, p0_1]
                  · linarith only [h707, h746, hlam]
                · linarith only [h667, h745, hlam]
            · linarith only [h736, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h753 | h753
            · rcases m.htr 0 1 4 (by decide) (by decide) with h754 | h754
              · rcases m.htr 0 1 5 (by decide) (by decide) with h755 | h755
                · rcases m.htr 0 2 5 (by decide) (by decide) with h756 | h756
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h757 | h757
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h758 | h758
                      · linarith only [h758, hlam, p0_0]
                      · linarith only [h758, hc04, hc45, hlam, hphi, p0_1]
                    · linarith only [h735, h757, hlam]
                  · linarith only [h707, h756, hlam]
                · linarith only [h667, h755, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h764 | h764
                · rcases m.htr 0 2 5 (by decide) (by decide) with h765 | h765
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h766 | h766
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h767 | h767
                      · linarith only [h767, hlam, p0_0]
                      · linarith only [h754, h767, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h735, h766, hlam]
                  · linarith only [h707, h765, hlam]
                · linarith only [h667, h764, hlam]
            · linarith only [h753, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h774 | h774
    · linarith only [h774, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h776 | h776
      · linarith only [h776, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h778 | h778
        · rcases p0_3 (m.d 3 5) (by simp) with h779 | h779
          · rcases p0_3 (m.d 4 5) (by simp) with h780 | h780
            · rcases m.htr 0 1 4 (by decide) (by decide) with h781 | h781
              · rcases m.htr 0 1 5 (by decide) (by decide) with h782 | h782
                · linarith only [h774, h782, hlam]
                · linarith only [h778, h781, h782, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h785 | h785
                · linarith only [h774, h785, hlam]
                · linarith only [h785, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h780, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h789 | h789
            · rcases m.htr 0 1 4 (by decide) (by decide) with h790 | h790
              · rcases m.htr 0 1 5 (by decide) (by decide) with h791 | h791
                · linarith only [h774, h791, hlam]
                · linarith only [h790, h791, hc14, hc45, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h794 | h794
                · linarith only [h774, h794, hlam]
                · linarith only [h794, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h789, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h798 | h798
          · rcases p0_3 (m.d 4 5) (by simp) with h799 | h799
            · rcases m.htr 0 1 4 (by decide) (by decide) with h800 | h800
              · rcases m.htr 0 1 5 (by decide) (by decide) with h801 | h801
                · linarith only [h774, h801, hlam]
                · linarith only [h800, h801, hc14, hc45, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h804 | h804
                · linarith only [h774, h804, hlam]
                · linarith only [h804, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h799, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h808 | h808
            · rcases m.htr 0 1 4 (by decide) (by decide) with h809 | h809
              · rcases m.htr 0 1 5 (by decide) (by decide) with h810 | h810
                · linarith only [h774, h810, hlam]
                · linarith only [h810, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h813 | h813
                · linarith only [h774, h813, hlam]
                · linarith only [h813, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h808, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h817 | h817
    · linarith only [h817, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h819 | h819
      · rcases p0_3 (m.d 2 5) (by simp) with h820 | h820
        · linarith only [h820, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h822 | h822
          · rcases p0_3 (m.d 4 5) (by simp) with h823 | h823
            · rcases m.htr 0 1 4 (by decide) (by decide) with h824 | h824
              · rcases m.htr 0 1 5 (by decide) (by decide) with h825 | h825
                · linarith only [h819, h825, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h817, h819, h825, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h828 | h828
                · linarith only [h817, h819, h828, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h817, h819, h828, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h823, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h832 | h832
            · rcases m.htr 0 1 4 (by decide) (by decide) with h833 | h833
              · rcases m.htr 0 1 5 (by decide) (by decide) with h834 | h834
                · linarith only [h817, h819, h834, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h817, h819, h834, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h837 | h837
                · linarith only [h817, h819, h833, h837, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                · linarith only [h817, h819, h837, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h832, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h841 | h841
        · linarith only [h841, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h843 | h843
          · rcases p0_3 (m.d 4 5) (by simp) with h844 | h844
            · rcases m.htr 0 1 4 (by decide) (by decide) with h845 | h845
              · rcases m.htr 0 1 5 (by decide) (by decide) with h846 | h846
                · rcases m.htr 0 2 5 (by decide) (by decide) with h847 | h847
                  · linarith only [h817, h847, hlam]
                  · linarith only [h847, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h819, h845, h846, hc14, hc45, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h851 | h851
                · rcases m.htr 0 2 5 (by decide) (by decide) with h852 | h852
                  · linarith only [h817, h852, hlam]
                  · linarith only [h852, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h819, h851, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h844, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h857 | h857
            · rcases m.htr 0 1 4 (by decide) (by decide) with h858 | h858
              · rcases m.htr 0 1 5 (by decide) (by decide) with h859 | h859
                · rcases m.htr 0 2 5 (by decide) (by decide) with h860 | h860
                  · linarith only [h817, h860, hlam]
                  · linarith only [h860, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h819, h858, h859, hc14, hc45, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h864 | h864
                · rcases m.htr 0 2 5 (by decide) (by decide) with h865 | h865
                  · linarith only [h817, h865, hlam]
                  · linarith only [h865, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h819, h864, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h857, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h870 | h870
    · linarith only [h870, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h872 | h872
      · rcases p0_3 (m.d 2 5) (by simp) with h873 | h873
        · rcases p0_3 (m.d 3 5) (by simp) with h874 | h874
          · linarith only [h874, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h876 | h876
            · rcases m.htr 0 1 4 (by decide) (by decide) with h877 | h877
              · rcases m.htr 0 1 5 (by decide) (by decide) with h878 | h878
                · linarith only [h872, h878, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h870, h872, h878, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h881 | h881
                · linarith only [h870, h872, h877, h881, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                · linarith only [h870, h872, h881, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h876, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h885 | h885
          · linarith only [h885, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h887 | h887
            · rcases m.htr 0 1 4 (by decide) (by decide) with h888 | h888
              · rcases m.htr 0 1 5 (by decide) (by decide) with h889 | h889
                · linarith only [h870, h872, h889, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h870, h872, h888, h889, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h892 | h892
                · linarith only [h870, h872, h892, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h870, h872, h892, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h887, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h896 | h896
        · rcases p0_3 (m.d 3 5) (by simp) with h897 | h897
          · linarith only [h897, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h899 | h899
            · rcases m.htr 0 1 4 (by decide) (by decide) with h900 | h900
              · rcases m.htr 0 1 5 (by decide) (by decide) with h901 | h901
                · rcases m.htr 0 2 5 (by decide) (by decide) with h902 | h902
                  · linarith only [h870, h896, h901, h902, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h870, h902, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h872, h900, h901, hc14, hc45, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h906 | h906
                · rcases m.htr 0 2 5 (by decide) (by decide) with h907 | h907
                  · linarith only [h870, h896, h906, h907, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h870, h907, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h872, h906, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h899, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h912 | h912
          · linarith only [h912, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h914 | h914
            · rcases m.htr 0 1 4 (by decide) (by decide) with h915 | h915
              · rcases m.htr 0 1 5 (by decide) (by decide) with h916 | h916
                · rcases m.htr 0 2 5 (by decide) (by decide) with h917 | h917
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h918 | h918
                    · linarith only [h870, h918, hlam]
                    · linarith only [h918, hc03, hc45, hlam, hphi, ht34, p0_1]
                  · linarith only [h896, h917, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h872, h915, h916, hc14, hc45, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h923 | h923
                · rcases m.htr 0 2 5 (by decide) (by decide) with h924 | h924
                  · rcases m.htr 0 3 5 (by decide) (by decide) with h925 | h925
                    · linarith only [h870, h925, hlam]
                    · linarith only [h925, hc03, hc45, hlam, hphi, ht34, p0_1]
                  · linarith only [h896, h924, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h872, h923, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h914, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_H_L_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0elo := hb0.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
          · linarith only [h0, h2, h5, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
            · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
              · linarith only [h0, h2, h4, h8, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h10, h2, h4, h7, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
                  · linarith only [h0, h12, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h0, h12, h2, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h15 | h15
              · linarith only [h0, h15, h2, h4, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h17 | h17
                · linarith only [h17, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h19, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h0, h19, h2, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h22 | h22
          · linarith only [h1, h2, h22, h4, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h24 | h24
            · rcases m.htr 0 3 5 (by decide) (by decide) with h25 | h25
              · linarith only [h1, h2, h25, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h27 | h27
                · linarith only [h1, h2, h24, h27, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
                  · linarith only [h0, h2, h29, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
                    · linarith only [h0, h22, h31, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                      · linarith only [h1, h33, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1, h2, h24, h29, h33, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h36 | h36
              · linarith only [h1, h2, h36, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h38 | h38
                · linarith only [h38, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
                  · linarith only [h0, h2, h4, h40, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
                    · linarith only [h0, h22, h42, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                      · linarith only [h1, h24, h4, h44, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h46 | h46
                        · linarith only [h1, h36, h46, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h48 | h48
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h49 | h49
                            · linarith only [h0, h2, h46, h49, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h51 | h51
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h52 | h52
                                · rcases h5bigk with h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h2, hlam, p53_1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h22, hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h36, hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h38, hlam, p53_1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h1, h2, h40, h42, hc12, hc25, hlam, hphi, p53_1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h42, hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h46, hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h24, h38, h46, h52, hc03, hc34, hlam, hphi, p53_1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h1, h2, h40, hc12, hc25, hlam, hphi, p53_1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h1, h2, h40, hc12, hc25, hlam, hphi, p53_1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h49, hlam, p53_1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h1, h24, h38, h40, h49, h52, hc12, hc34, hlam, hphi, ht23, p53_1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h1, h2, h40, h52, hc12, hc34, hlam, hphi, ht23, p53_1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h1, h2, h40, h52, hc12, hc34, hlam, hphi, ht23, p53_1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h0, h22, h52, hc12, hc34, hlam, hphi, ht23, p53_1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h1, h24, h38, h40, h52, hc12, hc34, hlam, hphi, ht23, p53_1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h1, h2, h40, hc12, hc45, hlam, hphi, ht23, ht34, p53_1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h48, hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h51, hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h52, hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [hlam, p53_0]
                                · linarith only [h44, h48, h52, hlam]
                              · linarith only [h1, h2, h40, h42, h44, h48, h51, hc12, hc34, hlam, hphi, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h81 | h81
                            · linarith only [h1, h2, h40, h46, h81, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h83 | h83
                              · linarith only [h1, h2, h40, h48, h83, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h85 | h85
                                · linarith only [h1, h2, h40, h42, h83, h85, hc12, hc34, hlam, hphi, ht23]
                                · rcases h5bigk with h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [hlam, p87_0]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h2, hlam, p87_1]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h22, hlam, p87_0]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h36, hlam, p87_0]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h38, hlam, p87_1]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h1, h2, h40, h42, hc12, hc25, hlam, hphi, p87_1]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [hlam, p87_0]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h42, hlam, p87_0]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h46, hlam, p87_0]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h48, hlam, p87_1]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h1, h2, h40, h81, h85, hc12, hc45, hlam, hphi, ht23, ht34, p87_1]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h1, h2, h40, h81, h85, hc12, hc45, hlam, hphi, ht23, ht34, p87_1]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [hlam, p87_0]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h81, hlam, p87_1]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h83, hlam, p87_1]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h1, h2, h40, h85, hc12, hc45, hlam, hphi, ht23, ht34, p87_1]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h1, h2, h40, h85, hc12, hc45, hlam, hphi, ht23, ht34, p87_1]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h0, h22, h85, hc12, hc45, hlam, hphi, ht23, ht34, p87_1]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [hlam, p87_0]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h85, hlam, p87_1]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h1, h2, h40, hc12, hc45, hlam, hphi, ht23, ht34, p87_1]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h1, h2, h40, hc12, hc45, hlam, hphi, ht23, ht34, p87_1]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h1, h2, h40, h42, hc12, hc45, hlam, hphi, ht23, ht34, p87_1]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [h81, hc23, hc45, hlam, hphi, ht34, p87_1]
                                  · have p87_0 := h87c.1
                                    have p87_1 := h87c.2.1
                                    have p87_2 := h87c.2.2.1
                                    have p87_3 := h87c.2.2.2
                                    linarith only [hlam, p87_0]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h113 | h113
      · linarith only [h113, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h115 | h115
        · linarith only [h0, h1, h115, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h117 | h117
          · linarith only [h0, h117, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h119 | h119
            · rcases m.htr 0 3 5 (by decide) (by decide) with h120 | h120
              · linarith only [h120, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h122 | h122
                · linarith only [h122, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h124 | h124
                  · linarith only [h0, h1, h115, h120, h124, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h126 | h126
                    · linarith only [h0, h117, h126, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h128 | h128
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h129 | h129
                        · linarith only [h0, h1, h120, h124, h129, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h129, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h128, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h133 | h133
              · linarith only [h133, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h135 | h135
                · linarith only [h135, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h137 | h137
                  · linarith only [h0, h1, h119, h135, h137, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h139 | h139
                    · linarith only [h0, h1, h119, h135, h139, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h141 | h141
                      · linarith only [h0, h1, h119, h137, h141, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h141, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h144 | h144
    · rcases m.htr 0 1 5 (by decide) (by decide) with h145 | h145
      · linarith only [h145, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h147 | h147
        · rcases m.htr 0 2 5 (by decide) (by decide) with h148 | h148
          · linarith only [h148, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h150 | h150
            · rcases m.htr 0 3 5 (by decide) (by decide) with h151 | h151
              · linarith only [h0, h144, h148, h151, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h153 | h153
                · linarith only [h0, h144, h148, h150, h153, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h155 | h155
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h156 | h156
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h157 | h157
                      · linarith only [h0, h144, h148, h157, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · linarith only [h0, h144, h148, h150, h157, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h160 | h160
                      · linarith only [h0, h144, h148, h160, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · linarith only [h0, h144, h148, h150, h160, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h147, h148, h155, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h164 | h164
              · linarith only [h0, h144, h148, h164, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h166 | h166
                · linarith only [h166, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h168 | h168
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h169 | h169
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h170 | h170
                      · linarith only [h0, h144, h148, h150, h170, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h172 | h172
                        · linarith only [h144, h164, h172, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h174 | h174
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h175 | h175
                            · linarith only [h144, h168, h172, h175, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h177 | h177
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h178 | h178
                                · rcases h5bigk with h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [hlam, p179_0]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h145, hlam, p179_1]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h148, hlam, p179_0]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h164, hlam, p179_0]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h166, hlam, p179_1]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h0, h144, h148, h168, h172, hc23, hc35, hlam, hphi, p179_1]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [hlam, p179_0]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h0, h144, h148, h168, h172, hc23, hc35, hlam, hphi, p179_1]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h172, hlam, p179_0]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h150, h166, h170, h174, hc03, hc34, hlam, hphi, p179_1]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h0, h144, h148, h168, h169, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p179_1]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h169, hlam, p179_1]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [hlam, p179_0]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h175, hlam, p179_1]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h0, h144, h148, h166, h168, h169, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p179_1]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h0, h144, h148, h168, hc23, hc35, hlam, hphi, p179_1]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h144, h145, h168, hc23, hc35, hlam, hphi, p179_1]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h0, h144, h148, h168, hc23, hc35, hlam, hphi, p179_1]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [hlam, p179_0]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h0, h144, h148, h166, h168, h178, hc23, hc34, hlam, hphi, p179_1]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h0, h144, h148, h168, h177, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p179_1]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h174, hlam, p179_0]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h177, hlam, p179_0]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [h178, hlam, p179_0]
                                  · have p179_0 := h179c.1
                                    have p179_1 := h179c.2.1
                                    have p179_2 := h179c.2.2.1
                                    have p179_3 := h179c.2.2.2
                                    linarith only [hlam, p179_0]
                                · linarith only [h170, h174, h178, hlam]
                              · linarith only [h0, h144, h148, h168, h170, h174, h177, hc23, hc34, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h207 | h207
                            · linarith only [h144, h168, h207, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h209 | h209
                              · linarith only [h169, h174, h209, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h211 | h211
                                · linarith only [h0, h144, h148, h169, h174, h211, hc13, hc34, hlam, hphi]
                                · rcases h5bigk with h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [hlam, p213_0]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h145, hlam, p213_1]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h148, hlam, p213_0]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h164, hlam, p213_0]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h166, hlam, p213_1]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h0, h144, h148, h168, h172, hc23, hc35, hlam, hphi, p213_1]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [hlam, p213_0]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h0, h144, h148, h168, h172, h211, hc23, hc45, hlam, hphi, ht34, p213_1]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h172, hlam, p213_0]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h174, hlam, p213_1]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h0, h144, h148, h168, h169, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p213_1]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h169, hlam, p213_1]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [hlam, p213_0]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h207, hlam, p213_1]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h209, hlam, p213_1]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h0, h144, h148, h168, h211, hc23, hc45, hlam, hphi, ht34, p213_1]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h144, h145, h168, h211, hc23, hc45, hlam, hphi, ht34, p213_1]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h0, h144, h148, h168, h211, hc23, hc45, hlam, hphi, ht34, p213_1]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [hlam, p213_0]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h211, hlam, p213_1]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h0, h144, h148, h168, hc23, hc45, hlam, hphi, ht34, p213_1]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h0, h144, h148, h168, h169, hc23, hc45, hlam, hphi, ht34, p213_1]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h0, h144, h148, h168, hc23, hc45, hlam, hphi, ht34, p213_1]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [h144, h164, h168, hc23, hc45, hlam, hphi, ht34, p213_1]
                                  · have p213_0 := h213c.1
                                    have p213_1 := h213c.2.1
                                    have p213_2 := h213c.2.2.1
                                    have p213_3 := h213c.2.2.2
                                    linarith only [hlam, p213_0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h239 | h239
                      · linarith only [h144, h239, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h241 | h241
                        · linarith only [h0, h144, h148, h164, h241, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h243 | h243
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h244 | h244
                            · linarith only [h0, h144, h168, h169, h241, h244, hlam]
                            · linarith only [h0, h144, h169, h244, hc13, hc35, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h247 | h247
                            · linarith only [h0, h144, h148, h168, h247, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                            · linarith only [h0, h144, h168, h169, h247, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h144, h147, h168, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
        · linarith only [h0, h144, h147, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h252 | h252
      · linarith only [h0, h252, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h254 | h254
        · rcases m.htr 0 2 5 (by decide) (by decide) with h255 | h255
          · linarith only [h255, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h257 | h257
            · rcases m.htr 0 3 5 (by decide) (by decide) with h258 | h258
              · linarith only [h254, h255, h258, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h260 | h260
                · linarith only [h260, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h262 | h262
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h263 | h263
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h265 | h265
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h266 | h266
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h267 | h267
                            · linarith only [h144, h254, h255, h258, h267, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h269 | h269
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h270 | h270
                                · linarith only [h257, h260, h270, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                · linarith only [h267, h269, h270, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h273 | h273
                                · linarith only [h254, h257, h269, h273, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases h5bigk with h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [hlam, p275_0]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h252, hlam, p275_1]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h255, hlam, p275_0]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h258, hlam, p275_0]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h260, hlam, p275_1]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    rcases p275_3 (m.d 0 5) (by simp) with h281 | h281
                                    · linarith only [h252, h281, hlam]
                                    · rcases p275_3 (m.d 1 5) (by simp) with h283 | h283
                                      · rcases p275_3 (m.d 2 5) (by simp) with h284 | h284
                                        · linarith only [h263, h284, hlam]
                                        · linarith only [h255, h284, hlam]
                                      · linarith only [h252, h283, hlam]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [hlam, p275_0]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h0, h255, h262, h264, h266, hc01, hc12, hlam, hphi, p275_1]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h257, h258, h262, h264, h266, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p275_1]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h254, h255, h262, h264, h266, h269, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p275_1]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h254, h255, h267, hc23, hc35, hlam, hphi, p275_1]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h263, hlam, p275_1]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [hlam, p275_0]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h267, hlam, p275_1]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h269, hlam, p275_1]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h254, h255, hc23, hc35, hlam, hphi, p275_1]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h265, hlam, p275_1]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h254, h255, hc23, hc35, hlam, hphi, p275_1]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [hlam, p275_0]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h273, hlam, p275_1]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h254, h255, hc23, hc45, hlam, hphi, ht34, p275_1]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h266, hlam, p275_0]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h254, h255, h262, h264, h266, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p275_1]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [h262, h264, h266, hc12, hlam, hphi, ht01, ht0b, ht5b, p275_1, u5ehi3]
                                  · have p275_0 := h275c.1
                                    have p275_1 := h275c.2.1
                                    have p275_2 := h275c.2.2.1
                                    have p275_3 := h275c.2.2.2
                                    linarith only [hlam, p275_0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h307 | h307
                            · linarith only [h254, h257, h258, h307, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h309 | h309
                              · linarith only [h265, h266, h307, h309, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h311 | h311
                                · linarith only [h255, h257, h265, h266, h307, h311, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                                · rcases h5bigk with h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [hlam, p313_0]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h252, hlam, p313_1]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h255, hlam, p313_0]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h258, hlam, p313_0]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h260, hlam, p313_1]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h254, h255, h266, hc23, hc45, hlam, hphi, ht34, p313_1]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [hlam, p313_0]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h254, h255, h266, hc23, hc45, hlam, hphi, ht34, p313_1]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h258, h266, hc03, hc45, hlam, hphi, ht34, p313_1]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h266, hlam, p313_1]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h254, h255, h263, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p313_1]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h263, hlam, p313_1]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [hlam, p313_0]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h307, hlam, p313_1]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h309, hlam, p313_1]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h254, h255, hc23, hc35, hlam, hphi, p313_1]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h265, hlam, p313_1]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h262, h265, hc12, hlam, hphi, ht01, ht0b, ht5b, p313_1, u5ehi2]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [hlam, p313_0]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h311, hlam, p313_1]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h254, h255, hc23, hc45, hlam, hphi, ht34, p313_1]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h252, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p313_1]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h254, h255, hc23, hc45, hlam, hphi, ht34, p313_1]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [h254, h255, h307, hc23, hc45, hlam, hphi, ht34, p313_1]
                                  · have p313_0 := h313c.1
                                    have p313_1 := h313c.2.1
                                    have p313_2 := h313c.2.2.1
                                    have p313_3 := h313c.2.2.2
                                    linarith only [hlam, p313_0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h339 | h339
                          · linarith only [h254, h255, h260, h264, h265, h339, hc23, hc35, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h341 | h341
                            · linarith only [h254, h265, h341, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h343 | h343
                              · linarith only [h263, h339, h343, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h345 | h345
                                · linarith only [h254, h255, h257, h263, h339, h345, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                · rcases h5bigk with h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [hlam, p347_0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h252, hlam, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h255, hlam, p347_0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h258, hlam, p347_0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h260, hlam, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h254, h255, h265, hc23, hc35, hlam, hphi, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [hlam, p347_0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h254, h255, h265, h345, hc23, hc45, hlam, hphi, ht34, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h265, hlam, p347_0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h339, hlam, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h254, h255, h263, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h263, hlam, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [hlam, p347_0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h341, hlam, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h343, hlam, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h254, h255, h345, hc23, hc45, hlam, hphi, ht34, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h252, h345, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h254, h255, h345, hc23, hc45, hlam, hphi, ht34, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [hlam, p347_0]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h345, hlam, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h254, h255, hc23, hc45, hlam, hphi, ht34, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h254, h255, h263, hc23, hc45, hlam, hphi, ht34, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h254, h255, hc23, hc45, hlam, hphi, ht34, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [h265, hc13, hc45, hlam, hphi, ht34, p347_1]
                                  · have p347_0 := h347c.1
                                    have p347_1 := h347c.2.1
                                    have p347_2 := h347c.2.2.1
                                    have p347_3 := h347c.2.2.2
                                    linarith only [hlam, p347_0]
                      · linarith only [h144, h254, h257, h264, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h374 | h374
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h375 | h375
                        · linarith only [h257, h258, h262, h263, h375, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h377 | h377
                          · linarith only [h254, h255, h260, h374, h375, h377, hc23, hc35, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h379 | h379
                            · linarith only [h254, h375, h379, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h381 | h381
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h382 | h382
                                · linarith only [h257, h377, h382, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                · linarith only [h144, h262, h263, h379, h381, h382, hc01, hc24, hlam, hphi, ht12]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h385 | h385
                                · linarith only [h144, h254, h257, h262, h263, h381, h385, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                · rcases h5bigk with h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [hlam, p387_0]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h252, hlam, p387_1]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h255, hlam, p387_0]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h258, hlam, p387_0]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h260, hlam, p387_1]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h254, h255, h263, h379, h385, hc23, hc45, hlam, hphi, ht34, p387_1]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [hlam, p387_0]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h263, hlam, p387_0]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h375, hlam, p387_0]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h377, hlam, p387_1]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h254, h255, h379, h385, hc23, hc45, hlam, hphi, ht34, p387_1]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h252, h379, h385, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p387_1]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [hlam, p387_0]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h379, hlam, p387_1]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h381, hlam, p387_1]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h254, h255, h385, hc23, hc45, hlam, hphi, ht34, p387_1]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h0, h263, h385, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p387_1]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h254, h255, h385, hc23, hc45, hlam, hphi, ht34, p387_1]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [hlam, p387_0]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h385, hlam, p387_1]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h254, h255, hc23, hc45, hlam, hphi, ht34, p387_1]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h144, h262, h263, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p387_1]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h144, h262, h263, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p387_1]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [h258, hc03, hc45, hlam, hphi, ht34, p387_1]
                                  · have p387_0 := h387c.1
                                    have p387_1 := h387c.2.1
                                    have p387_2 := h387c.2.2.1
                                    have p387_3 := h387c.2.2.2
                                    linarith only [hlam, p387_0]
                      · linarith only [h144, h257, h374, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h254, h262, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h415 | h415
              · linarith only [h254, h255, h415, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h417 | h417
                · linarith only [h417, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h419 | h419
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h420 | h420
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h421 | h421
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h422 | h422
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h423 | h423
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h424 | h424
                            · linarith only [h254, h415, h424, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h426 | h426
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h427 | h427
                                · linarith only [h144, h257, h417, h419, h421, h427, hc01, hc12, hlam, hphi]
                                · linarith only [h144, h257, h426, h427, hc01, hc24, hlam, hphi, ht12]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h430 | h430
                                · linarith only [h254, h255, h426, h430, hc23, hc34, hlam, hphi]
                                · linarith only [h144, h257, h419, h421, h423, h430, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h433 | h433
                            · linarith only [h254, h433, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h435 | h435
                              · linarith only [h144, h257, h421, h423, h435, hc01, hc24, hlam, hphi, ht12]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h437 | h437
                                · linarith only [h421, h423, h437, hlam]
                                · rcases h5bigk with h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [hlam, p439_0]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h252, hlam, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h255, hlam, p439_0]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h415, hlam, p439_0]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h417, hlam, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h254, h255, h423, hc23, hc45, hlam, hphi, ht34, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [hlam, p439_0]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h254, h255, h423, hc23, hc45, hlam, hphi, ht34, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h254, h255, h423, h433, hc23, hc45, hlam, hphi, ht34, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h423, hlam, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h254, h255, h433, hc23, hc35, hlam, hphi, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h420, hlam, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [hlam, p439_0]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h433, hlam, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h435, hlam, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h254, h255, hc23, hc35, hlam, hphi, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h422, hlam, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h254, h255, hc23, hc35, hlam, hphi, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [hlam, p439_0]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h437, hlam, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h254, h255, hc23, hc45, hlam, hphi, ht34, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h252, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h254, h255, hc23, hc45, hlam, hphi, ht34, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [h254, h255, h433, hc23, hc45, hlam, hphi, ht34, p439_1]
                                  · have p439_0 := h439c.1
                                    have p439_1 := h439c.2.1
                                    have p439_2 := h439c.2.2.1
                                    have p439_3 := h439c.2.2.2
                                    linarith only [hlam, p439_0]
                        · linarith only [h144, h257, h421, h422, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h466 | h466
                        · linarith only [h144, h415, h421, h466, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h468 | h468
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h469 | h469
                            · linarith only [h254, h466, h469, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h471 | h471
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h472 | h472
                                · rcases h5bigk with h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h252, hlam, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h255, hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h415, hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h417, hlam, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h254, h255, h466, hc23, hc35, hlam, hphi, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h254, h255, h466, hc23, hc35, hlam, hphi, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h466, hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h144, h257, h417, h421, h468, hc01, hc34, hlam, hphi, ht12, ht23, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h254, h255, h420, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h420, hlam, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h469, hlam, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h144, h257, h417, h420, hc01, hc12, hlam, hphi, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h254, h255, hc23, hc35, hlam, hphi, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h252, hc01, hc35, hlam, hphi, ht12, ht23, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h254, h255, hc23, hc35, hlam, hphi, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h144, h257, h417, h472, hc01, hc34, hlam, hphi, ht12, ht23, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h254, h255, h471, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h468, hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h471, hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h472, hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [hlam, p473_0]
                                · linarith only [h421, h468, h472, hlam]
                              · linarith only [h254, h255, h421, h468, h471, hc23, hc34, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h501 | h501
                            · linarith only [h254, h501, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h503 | h503
                              · linarith only [h144, h421, h468, h503, hc01, hc24, hlam, hphi, ht12]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h505 | h505
                                · linarith only [h144, h421, h468, h505, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h144, h421, h505, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h508 | h508
                      · linarith only [h144, h257, h419, h420, h508, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h510 | h510
                        · linarith only [h144, h415, h419, h420, h510, hc01, hc25, hlam, hphi, ht12]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h512 | h512
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h513 | h513
                            · linarith only [h254, h255, h510, h513, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h515 | h515
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h516 | h516
                                · rcases h5bigk with h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [hlam, p517_0]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h252, hlam, p517_1]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h255, hlam, p517_0]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h415, hlam, p517_0]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h417, hlam, p517_1]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h254, h255, h420, h513, h516, hc23, hc34, hlam, hphi, p517_1]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [hlam, p517_0]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h420, hlam, p517_0]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h510, hlam, p517_0]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h144, h257, h417, h420, h513, h516, hc01, hc34, hlam, hphi, ht12, ht23, p517_1]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h254, h255, h513, h516, hc23, hc34, hlam, hphi, p517_1]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h252, h513, h516, hc01, hc34, hlam, hphi, ht12, ht23, p517_1]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [hlam, p517_0]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h513, hlam, p517_1]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h144, h257, h417, h513, h516, hc01, hc34, hlam, hphi, ht12, ht23, p517_1]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h254, h255, h516, hc23, hc34, hlam, hphi, p517_1]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h144, h257, h417, h512, h516, hc01, hc34, hlam, hphi, ht12, ht23, p517_1]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h254, h255, h516, hc23, hc34, hlam, hphi, p517_1]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [hlam, p517_0]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h144, h257, h417, h516, hc01, hc34, hlam, hphi, ht12, ht23, p517_1]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h254, h255, h512, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p517_1]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h512, hlam, p517_0]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h515, hlam, p517_0]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [h516, hlam, p517_0]
                                  · have p517_0 := h517c.1
                                    have p517_1 := h517c.2.1
                                    have p517_2 := h517c.2.2.1
                                    have p517_3 := h517c.2.2.2
                                    linarith only [hlam, p517_0]
                                · linarith only [h508, h512, h516, hlam]
                              · linarith only [h144, h419, h420, h508, h512, h515, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h545 | h545
                            · linarith only [h254, h255, h510, h545, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h547 | h547
                              · linarith only [h144, h508, h512, h547, hc01, hc24, hlam, hphi, ht12]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h549 | h549
                                · linarith only [h0, h420, h547, h549, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h144, h508, h549, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h254, h419, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h553 | h553
          · linarith only [h553, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h555 | h555
            · rcases m.htr 0 3 5 (by decide) (by decide) with h556 | h556
              · linarith only [h556, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h558 | h558
                · linarith only [h558, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h560 | h560
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h561 | h561
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h562 | h562
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h563 | h563
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h564 | h564
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h565 | h565
                            · linarith only [h555, h556, h560, h565, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h254, h563, h565, hc01, hc13, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h568 | h568
                            · linarith only [h555, h556, h560, h568, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h254, h563, h568, hc01, hc13, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h571 | h571
                          · linarith only [h562, h563, h571, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h573 | h573
                            · linarith only [h144, h563, h573, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h575 | h575
                              · linarith only [h561, h571, h575, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h577 | h577
                                · linarith only [h555, h556, h571, h577, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                                · rcases h5bigk with h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h252, hlam, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h553, hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h556, hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h558, hlam, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h555, h556, h563, h577, hc34, hc45, hlam, hphi, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h0, h254, h563, h573, h577, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h563, hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h571, hlam, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h555, h556, h561, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h561, hlam, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h573, hlam, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h575, hlam, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h555, h556, h577, hc34, hc45, hlam, hphi, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h252, h577, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h0, h553, h577, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h577, hlam, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h555, h556, hc34, hc45, hlam, hphi, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h0, h254, h560, h563, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h0, h254, h573, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h555, h556, hc34, hc45, hlam, hphi, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [hlam, p579_0]
                      · linarith only [h0, h254, h555, h560, h562, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h254, h560, h561, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h607 | h607
                    · linarith only [h0, h553, h560, h607, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h609 | h609
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h610 | h610
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h611 | h611
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h612 | h612
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h613 | h613
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h614 | h614
                                · linarith only [h555, h558, h614, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi0]
                                · rcases h5bigk with h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [hlam, p616_0]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h252, hlam, p616_1]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h553, hlam, p616_0]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h556, hlam, p616_0]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h558, hlam, p616_1]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    rcases p616_3 (m.d 0 5) (by simp) with h622 | h622
                                    · linarith only [h252, h622, hlam]
                                    · rcases p616_3 (m.d 1 5) (by simp) with h624 | h624
                                      · rcases p616_3 (m.d 2 5) (by simp) with h625 | h625
                                        · rcases p616_3 (m.d 3 5) (by simp) with h626 | h626
                                          · linarith only [h610, h626, hlam]
                                          · linarith only [h556, h626, hlam]
                                        · linarith only [h553, h625, hlam]
                                      · linarith only [h252, h624, hlam]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [hlam, p616_0]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h607, hlam, p616_0]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h555, h556, h560, h609, h611, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p616_1]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h555, h556, h560, h609, h611, h614, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p616_1]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    rcases p616_3 (m.d 0 5) (by simp) with h635 | h635
                                    · linarith only [h553, h635, hlam]
                                    · rcases p616_3 (m.d 1 5) (by simp) with h637 | h637
                                      · linarith only [h607, h637, hlam]
                                      · linarith only [h252, h637, hlam]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h252, h612, hc01, hc23, hlam, hphi, ht12, p616_1]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [hlam, p616_0]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h555, h556, h612, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p616_1]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h555, h556, h612, h614, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p616_1]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h555, h556, h614, hc34, hc45, hlam, hphi, p616_1]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h610, hlam, p616_1]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h612, hlam, p616_0]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [hlam, p616_0]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h614, hlam, p616_1]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h555, h556, hc34, hc45, hlam, hphi, p616_1]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h611, hlam, p616_0]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h613, hlam, p616_0]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [h555, h556, hc34, hc45, hlam, hphi, p616_1]
                                  · have p616_0 := h616c.1
                                    have p616_1 := h616c.2.1
                                    have p616_2 := h616c.2.2.1
                                    have p616_3 := h616c.2.2.2
                                    linarith only [hlam, p616_0]
                              · linarith only [h0, h560, h607, h609, h611, h613, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h560, h612, hc01, hc35, hlam, hphi, ht12, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h656 | h656
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h657 | h657
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h658 | h658
                                · linarith only [h555, h611, h658, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                · rcases h5bigk with h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [hlam, p660_0]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h252, hlam, p660_1]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h553, hlam, p660_0]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h556, hlam, p660_0]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h558, hlam, p660_1]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h555, h556, h611, h657, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p660_1]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [hlam, p660_0]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h607, hlam, p660_0]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h611, h657, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p660_1, u5ehi3]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h611, hlam, p660_1]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    rcases p660_3 (m.d 0 5) (by simp) with h671 | h671
                                    · linarith only [h553, h671, hlam]
                                    · rcases p660_3 (m.d 1 5) (by simp) with h673 | h673
                                      · linarith only [h607, h673, hlam]
                                      · linarith only [h252, h673, hlam]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h252, hc01, hc25, hlam, hphi, ht12, p660_1]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [hlam, p660_0]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h555, h556, h656, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p660_1]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h555, h556, h610, h611, h656, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p660_1]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h555, h556, h560, h610, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p660_1]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h610, hlam, p660_1]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h656, hlam, p660_0]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [hlam, p660_0]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h658, hlam, p660_1]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h555, h556, hc34, hc45, hlam, hphi, p660_1]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h252, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p660_1]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h657, hlam, p660_0]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [h555, h556, h657, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p660_1]
                                  · have p660_0 := h660c.1
                                    have p660_1 := h660c.2.1
                                    have p660_2 := h660c.2.2.1
                                    have p660_3 := h660c.2.2.2
                                    linarith only [hlam, p660_0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h690 | h690
                                · linarith only [h555, h607, h657, h690, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi1]
                                · rcases h5bigk with h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [hlam, p692_0]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h252, hlam, p692_1]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h553, hlam, p692_0]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h556, hlam, p692_0]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h558, hlam, p692_1]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h555, h556, h607, h657, hc34, hc45, hlam, hphi, p692_1]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [hlam, p692_0]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h607, hlam, p692_0]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h555, h556, h607, h657, hc34, hc45, hlam, hphi, p692_1]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h611, hlam, p692_1]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h555, h556, h657, hc34, hc45, hlam, hphi, p692_1]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h252, h657, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p692_1]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [hlam, p692_0]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h555, h556, h657, hc34, hc45, hlam, hphi, p692_1]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h657, hlam, p692_1]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h555, h556, h607, h610, h657, hc34, hc45, hlam, hphi, p692_1]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h610, hlam, p692_1]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h656, hlam, p692_0]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [hlam, p692_0]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h690, hlam, p692_1]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h555, h556, hc34, hc45, hlam, hphi, p692_1]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h252, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p692_1]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h0, h553, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p692_1]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [h555, h556, hc34, hc45, hlam, hphi, p692_1]
                                  · have p692_0 := h692c.1
                                    have p692_1 := h692c.2.1
                                    have p692_2 := h692c.2.2.1
                                    have p692_3 := h692c.2.2.2
                                    linarith only [hlam, p692_0]
                            · linarith only [h0, h560, h610, h656, hc01, hc15, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h719 | h719
                          · linarith only [h609, h610, h719, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h721 | h721
                            · linarith only [h144, h610, h721, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h560, h721, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h555, h560, h609, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h725 | h725
              · linarith only [h555, h725, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h727 | h727
                · linarith only [h727, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h729 | h729
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h730 | h730
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h731 | h731
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h732 | h732
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h733 | h733
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h734 | h734
                            · linarith only [h144, h725, h729, h734, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h254, h729, h732, h734, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h737 | h737
                            · linarith only [h0, h254, h725, h729, h737, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h254, h729, h732, h737, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h254, h555, h731, h732, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h741 | h741
                        · linarith only [h0, h254, h725, h731, h741, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h743 | h743
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h744 | h744
                            · linarith only [h144, h741, h744, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h746 | h746
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h747 | h747
                                · rcases h5bigk with h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [hlam, p748_0]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h252, hlam, p748_1]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h553, hlam, p748_0]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h725, hlam, p748_0]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h727, hlam, p748_1]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    rcases p748_3 (m.d 0 5) (by simp) with h754 | h754
                                    · linarith only [h252, h754, hlam]
                                    · rcases p748_3 (m.d 1 5) (by simp) with h756 | h756
                                      · rcases p748_3 (m.d 2 5) (by simp) with h757 | h757
                                        · linarith only [h730, h757, hlam]
                                        · linarith only [h553, h757, hlam]
                                      · linarith only [h252, h756, hlam]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [hlam, p748_0]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h0, h553, h731, h743, hc01, hc34, hlam, hphi, ht12, ht23, p748_1]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h741, hlam, p748_0]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h0, h254, h555, h727, h731, h743, hc01, hc34, hlam, hphi, ht12, ht23, p748_1]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h0, h254, h555, h727, h730, hc01, hc12, hlam, hphi, p748_1]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h730, hlam, p748_1]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [hlam, p748_0]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h744, hlam, p748_1]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h0, h254, h555, h727, h730, hc01, hc12, hlam, hphi, p748_1]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    rcases p748_3 (m.d 0 5) (by simp) with h770 | h770
                                    · linarith only [h725, h770, hlam]
                                    · rcases p748_3 (m.d 1 5) (by simp) with h772 | h772
                                      · linarith only [h741, h772, hlam]
                                      · linarith only [h252, h772, hlam]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h252, h747, hc01, hc34, hlam, hphi, ht12, ht23, p748_1]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h0, h553, h747, hc01, hc34, hlam, hphi, ht12, ht23, p748_1]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [hlam, p748_0]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h0, h254, h555, h727, h747, hc01, hc34, hlam, hphi, ht12, ht23, p748_1]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h0, h254, h555, h727, h746, hc01, hc24, hlam, hphi, ht12, p748_1]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h743, hlam, p748_0]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h746, hlam, p748_0]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [h747, hlam, p748_0]
                                  · have p748_0 := h748c.1
                                    have p748_1 := h748c.2.1
                                    have p748_2 := h748c.2.2.1
                                    have p748_3 := h748c.2.2.2
                                    linarith only [hlam, p748_0]
                                · linarith only [h731, h743, h747, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h785 | h785
                                · rcases h5bigk with h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [hlam, p786_0]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h252, hlam, p786_1]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h553, hlam, p786_0]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h725, hlam, p786_0]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h727, hlam, p786_1]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    rcases p786_3 (m.d 0 5) (by simp) with h792 | h792
                                    · linarith only [h252, h792, hlam]
                                    · rcases p786_3 (m.d 1 5) (by simp) with h794 | h794
                                      · rcases p786_3 (m.d 2 5) (by simp) with h795 | h795
                                        · linarith only [h730, h795, hlam]
                                        · linarith only [h553, h795, hlam]
                                      · linarith only [h252, h794, hlam]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [hlam, p786_0]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h0, h553, hc01, hc15, hlam, hphi, p786_1]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h741, hlam, p786_0]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h0, h254, h555, h727, hc01, hc15, hlam, hphi, p786_1]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h0, h254, h555, h727, h730, hc01, hc12, hlam, hphi, p786_1]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h730, hlam, p786_1]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [hlam, p786_0]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h744, hlam, p786_1]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h746, hlam, p786_1]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    rcases p786_3 (m.d 0 5) (by simp) with h808 | h808
                                    · linarith only [h725, h808, hlam]
                                    · rcases p786_3 (m.d 1 5) (by simp) with h810 | h810
                                      · linarith only [h741, h810, hlam]
                                      · linarith only [h252, h810, hlam]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h252, h785, hc01, hc34, hlam, hphi, ht12, ht23, p786_1]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h0, h553, h785, hc01, hc34, hlam, hphi, ht12, ht23, p786_1]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [hlam, p786_0]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h0, h254, h555, h727, h785, hc01, hc34, hlam, hphi, ht12, ht23, p786_1]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h0, h254, h555, h727, h731, h743, hc01, hc34, hlam, hphi, ht12, ht23, p786_1]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h743, hlam, p786_0]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h0, h254, h731, h743, h744, hc01, hc34, hlam, hphi, ht12, ht23, p786_1]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [h785, hlam, p786_0]
                                  · have p786_0 := h786c.1
                                    have p786_1 := h786c.2.1
                                    have p786_2 := h786c.2.2.1
                                    have p786_3 := h786c.2.2.2
                                    linarith only [hlam, p786_0]
                                · linarith only [h731, h743, h785, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h823 | h823
                            · linarith only [h0, h254, h725, h729, h731, h743, h823, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h825 | h825
                              · linarith only [h144, h731, h743, h825, hc01, hc24, hlam, hphi, ht12]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h827 | h827
                                · linarith only [h0, h254, h729, h731, h743, h827, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h0, h254, h729, h731, h827, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h254, h729, h730, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h831 | h831
                    · linarith only [h0, h553, h729, h831, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h833 | h833
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h834 | h834
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h835 | h835
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h836 | h836
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h837 | h837
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h838 | h838
                                · linarith only [h0, h254, h555, h727, h833, h838, hc01, hc13, hlam, hphi]
                                · linarith only [h0, h254, h555, h835, h838, hc01, hc14, hlam, hphi]
                              · linarith only [h0, h729, h831, h833, h835, h837, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h729, h836, hc01, hc35, hlam, hphi, ht12, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h843 | h843
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h844 | h844
                              · linarith only [h0, h254, h555, h833, h835, h844, hc01, hc24, hlam, hphi, ht12]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h846 | h846
                                · linarith only [h833, h835, h846, hlam]
                                · rcases h5bigk with h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h252, hlam, p848_1]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h553, hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h725, hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h727, hlam, p848_1]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    rcases p848_3 (m.d 0 5) (by simp) with h854 | h854
                                    · linarith only [h252, h854, hlam]
                                    · rcases p848_3 (m.d 1 5) (by simp) with h856 | h856
                                      · rcases p848_3 (m.d 2 5) (by simp) with h857 | h857
                                        · rcases p848_3 (m.d 3 5) (by simp) with h858 | h858
                                          · linarith only [h834, h858, hlam]
                                          · linarith only [h725, h858, hlam]
                                        · linarith only [h553, h857, hlam]
                                      · linarith only [h252, h856, hlam]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h831, hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h0, h254, h555, h834, h846, hc01, hc13, hlam, hphi, p848_1]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h835, hlam, p848_1]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    rcases p848_3 (m.d 0 5) (by simp) with h867 | h867
                                    · linarith only [h553, h867, hlam]
                                    · rcases p848_3 (m.d 1 5) (by simp) with h869 | h869
                                      · linarith only [h831, h869, hlam]
                                      · linarith only [h252, h869, hlam]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h252, h844, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p848_1]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h0, h254, h555, h844, h846, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p848_1]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h844, hlam, p848_1]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h0, h254, h555, h727, h729, h834, hc01, hc23, hlam, hphi, ht12, p848_1]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h834, hlam, p848_1]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h843, hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h846, hlam, p848_1]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    rcases p848_3 (m.d 0 5) (by simp) with h881 | h881
                                    · linarith only [h727, h881, hlam]
                                    · rcases p848_3 (m.d 1 5) (by simp) with h883 | h883
                                      · linarith only [h835, h883, hlam]
                                      · linarith only [h252, h883, hlam]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h252, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p848_1]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h0, h553, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p848_1]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h0, h254, h725, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p848_1]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [hlam, p848_0]
                            · linarith only [h0, h729, h843, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h254, h555, h833, h834, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h892 | h892
                        · linarith only [h0, h254, h725, h833, h892, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h894 | h894
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h895 | h895
                            · linarith only [h144, h892, h895, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h729, h895, hc01, hc35, hlam, hphi, ht12, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h898 | h898
                            · linarith only [h0, h729, h892, h898, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h729, h898, hc01, hc35, hlam, hphi, ht12, ht23]

theorem n7l_sBT3_H_L_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h0, h2, h6, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h1, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
              · linarith only [h0, h11, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h0, h11, h2, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h1, h10, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h2, h3, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h16 | h16
        · rcases m.htr 0 4 5 (by decide) (by decide) with h17 | h17
          · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
            · rcases m.htr 1 3 4 (by decide) (by decide) with h19 | h19
              · linarith only [h0, h16, h19, h2, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                · linarith only [h0, h21, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h16, h21, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
            · linarith only [h1, h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h16, h17, h2, hc35, hlam, hphi, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
          · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
            · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
              · linarith only [h0, h2, h28, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                · linarith only [h0, h16, h30, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                  · linarith only [h0, h2, h27, h32, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                    · linarith only [h0, h16, h27, h34, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
                      · rcases h3bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1, u0elo2]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h16, hc23, hlam, hphi, ht34, ht45, p37_1, u5elo3]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h2, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h16, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h0, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1, u0elo0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h28, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h30, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h1, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h27, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h32, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h34, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          rcases p37_3 (m.d 0 3) (by simp) with h53 | h53
                          · linarith only [h53, hlam, p37_0]
                          · rcases p37_3 (m.d 1 3) (by simp) with h55 | h55
                            · linarith only [h28, h55, hlam]
                            · rcases p37_3 (m.d 2 3) (by simp) with h57 | h57
                              · linarith only [h32, h57, hlam]
                              · rcases p37_3 (m.d 3 4) (by simp) with h59 | h59
                                · rcases p37_3 (m.d 3 5) (by simp) with h60 | h60
                                  · linarith only [h36, h60, hlam]
                                  · linarith only [h16, h60, hlam]
                                · linarith only [h59, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          rcases p37_3 (m.d 0 3) (by simp) with h64 | h64
                          · linarith only [h2, h64, hlam]
                          · linarith only [h0, h64, hlam]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          rcases p37_3 (m.d 0 3) (by simp) with h67 | h67
                          · linarith only [h2, h67, hlam]
                          · linarith only [h1, h67, hlam]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h0, h16, h27, hc23, hc34, hlam, hphi, p37_1]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h0, h27, hc23, hlam, hphi, ht34, ht45, p37_1, u5elo3]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h27, hc23, hlam, hphi, ht34, ht45, p37_1, u5elo3]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hc23, hlam, hphi, ht34, ht45, p37_1, u5elo3]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h36, hlam, p37_1]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hlam, p37_0]
                      · linarith only [h26, h28, h36, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
            · linarith only [h1, h27, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
            · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
              · linarith only [h0, h2, h80, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h82 | h82
                · linarith only [h0, h82, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                  · linarith only [h0, h2, h26, h79, h84, hc34, hlam, hphi, ht45, u5elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h86 | h86
                    · linarith only [h0, h16, h2, h26, h79, h86, hc05, hlam, hphi, u5elo4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h88 | h88
                      · rcases h3bigk with h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [hlam, p89_0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h2, h26, h79, h88, hc23, hlam, hphi, ht34, ht45, p89_1, u5elo3]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h2, h26, h88, hc23, hlam, hphi, ht34, ht45, p89_1, u5elo3]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h2, hlam, p89_0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h16, hlam, p89_0]
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
                          linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p89_1, u0elo0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h80, hlam, p89_0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h82, hlam, p89_0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h1, hlam, p89_0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h79, hlam, p89_0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [hlam, p89_0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h84, hlam, p89_0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h86, hlam, p89_0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          rcases p89_3 (m.d 0 3) (by simp) with h105 | h105
                          · linarith only [h105, hlam, p89_0]
                          · rcases p89_3 (m.d 1 3) (by simp) with h107 | h107
                            · linarith only [h107, h80, hlam]
                            · rcases p89_3 (m.d 2 3) (by simp) with h109 | h109
                              · linarith only [h109, h84, hlam]
                              · rcases p89_3 (m.d 3 4) (by simp) with h111 | h111
                                · rcases p89_3 (m.d 3 5) (by simp) with h112 | h112
                                  · linarith only [h112, h88, hlam]
                                  · linarith only [h112, h16, hlam]
                                · linarith only [h111, hlam, p89_0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          rcases p89_3 (m.d 0 3) (by simp) with h116 | h116
                          · linarith only [h116, h2, hlam]
                          · linarith only [h0, h116, hlam]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          rcases p89_3 (m.d 0 3) (by simp) with h119 | h119
                          · linarith only [h119, h2, hlam]
                          · linarith only [h1, h119, hlam]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [hlam, p89_0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h2, h26, h88, hc03, hc34, hlam, hphi, p89_1]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h0, hc13, hlam, hphi, ht34, ht45, p89_1, u5elo3]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h79, hc23, hlam, hphi, ht34, ht45, p89_1, u5elo3]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [hc23, hlam, hphi, ht34, ht45, p89_1, u5elo3]
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
                      · linarith only [h0, h2, h79, h88, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h1, h79, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h131 | h131
      · rcases m.htr 0 3 5 (by decide) (by decide) with h132 | h132
        · rcases m.htr 0 4 5 (by decide) (by decide) with h133 | h133
          · rcases m.htr 1 2 3 (by decide) (by decide) with h134 | h134
            · linarith only [h0, h1, h134, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h136 | h136
              · linarith only [h0, h136, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h0, h131, h134, h136, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h139 | h139
            · linarith only [h0, h1, h131, h139, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h141 | h141
              · linarith only [h0, h141, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h131, h141, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
        · linarith only [h131, h132, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h145 | h145
        · rcases m.htr 0 4 5 (by decide) (by decide) with h146 | h146
          · rcases m.htr 1 2 3 (by decide) (by decide) with h147 | h147
            · linarith only [h0, h1, h147, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h149 | h149
              · linarith only [h0, h131, h145, h149, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h151 | h151
                · linarith only [h0, h151, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h145, h151, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
          · linarith only [h131, h145, h146, hc35, hlam, hphi, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h155 | h155
          · rcases m.htr 1 2 3 (by decide) (by decide) with h156 | h156
            · linarith only [h0, h1, h156, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h158 | h158
              · linarith only [h0, h131, h158, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h160 | h160
                · linarith only [h0, h145, h160, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h162 | h162
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h163 | h163
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h164 | h164
                      · rcases h3bigk with h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h156, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p165_1, u0elo2]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h1, hlam, p165_1]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h131, hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h145, hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h0, hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h156, hlam, p165_1]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h158, hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h160, hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          rcases p165_3 (m.d 0 3) (by simp) with h176 | h176
                          · linarith only [h1, h176, hlam]
                          · rcases p165_3 (m.d 1 3) (by simp) with h178 | h178
                            · linarith only [h156, h178, hlam]
                            · rcases p165_3 (m.d 2 3) (by simp) with h180 | h180
                              · rcases p165_3 (m.d 3 4) (by simp) with h181 | h181
                                · linarith only [h162, h181, hlam]
                                · linarith only [h131, h181, hlam]
                              · linarith only [h1, h180, hlam]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          rcases p165_3 (m.d 0 3) (by simp) with h185 | h185
                          · linarith only [h1, h185, hlam]
                          · linarith only [h0, h185, hlam]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h0, h131, h156, hc12, hc23, hlam, hphi, p165_1]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h0, h145, h156, hc12, hc23, hlam, hphi, p165_1]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h0, h156, h162, hc12, hc23, hlam, hphi, p165_1]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h156, h162, hc12, hc23, hlam, hphi, p165_1]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h162, hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h0, h145, h156, h162, hc12, hc23, hlam, hphi, p165_1]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h0, h156, h163, hc12, hlam, hphi, ht23, ht34, ht45, p165_1, u5elo2]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h156, h163, hc12, hlam, hphi, ht23, ht34, ht45, p165_1, u5elo2]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h163, hlam, p165_0]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [h164, hlam, p165_1]
                        · have p165_0 := h165c.1
                          have p165_1 := h165c.2.1
                          have p165_2 := h165c.2.2.1
                          have p165_3 := h165c.2.2.2
                          linarith only [hlam, p165_0]
                      · linarith only [h155, h164, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h1, h163, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h203 | h203
                    · linarith only [h0, h145, h156, h162, h203, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1, h203, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h206 | h206
            · linarith only [h0, h1, h206, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h208 | h208
              · linarith only [h0, h131, h155, h208, hc34, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h210 | h210
                · linarith only [h0, h131, h155, h210, hc35, hlam, hphi, u5elo4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h212 | h212
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h213 | h213
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h214 | h214
                      · linarith only [h0, h131, h155, h206, h212, h214, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h131, h206, h214, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h1, h213, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h218 | h218
                    · linarith only [h0, h145, h206, h212, h218, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1, h218, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h221 | h221
    · rcases m.htr 0 3 4 (by decide) (by decide) with h222 | h222
      · rcases m.htr 0 3 5 (by decide) (by decide) with h223 | h223
        · rcases m.htr 0 4 5 (by decide) (by decide) with h224 | h224
          · rcases m.htr 1 2 3 (by decide) (by decide) with h225 | h225
            · rcases m.htr 1 3 4 (by decide) (by decide) with h226 | h226
              · rcases m.htr 1 3 5 (by decide) (by decide) with h227 | h227
                · rcases m.htr 2 3 4 (by decide) (by decide) with h228 | h228
                  · linarith only [h221, h228, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h222, h228, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h223, h227, hlam]
              · linarith only [h0, h222, h226, hlam]
            · linarith only [h221, h225, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h234 | h234
            · rcases m.htr 1 3 4 (by decide) (by decide) with h235 | h235
              · rcases m.htr 1 3 5 (by decide) (by decide) with h236 | h236
                · rcases m.htr 2 3 4 (by decide) (by decide) with h237 | h237
                  · linarith only [h221, h237, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h221, h222, h237, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h223, h236, hlam]
              · linarith only [h0, h222, h235, hlam]
            · linarith only [h221, h234, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h222, h223, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h244 | h244
        · rcases m.htr 0 4 5 (by decide) (by decide) with h245 | h245
          · rcases m.htr 1 2 3 (by decide) (by decide) with h246 | h246
            · rcases m.htr 1 3 4 (by decide) (by decide) with h247 | h247
              · rcases m.htr 1 3 5 (by decide) (by decide) with h248 | h248
                · rcases m.htr 2 3 4 (by decide) (by decide) with h249 | h249
                  · linarith only [h221, h222, h244, h249, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h251 | h251
                    · linarith only [h221, h251, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h244, h251, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h222, h244, h247, h248, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h255 | h255
                · rcases m.htr 2 3 4 (by decide) (by decide) with h256 | h256
                  · linarith only [h0, h247, h256, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h258 | h258
                    · linarith only [h221, h258, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h244, h258, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h244, h255, hlam]
            · linarith only [h221, h246, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h222, h244, h245, hc35, hlam, hphi, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h264 | h264
          · rcases m.htr 1 2 3 (by decide) (by decide) with h265 | h265
            · rcases m.htr 1 3 4 (by decide) (by decide) with h266 | h266
              · rcases m.htr 1 3 5 (by decide) (by decide) with h267 | h267
                · rcases m.htr 2 3 4 (by decide) (by decide) with h268 | h268
                  · linarith only [h221, h222, h268, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h270 | h270
                    · linarith only [h221, h244, h270, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h272 | h272
                      · rcases h3bigk with h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [hlam, p273_0]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [h0, hlam, p273_1]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p273_1, u0elo2]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [h222, hlam, p273_0]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [h244, hlam, p273_0]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          rcases p273_3 (m.d 0 3) (by simp) with h279 | h279
                          · linarith only [h0, h279, hlam]
                          · rcases p273_3 (m.d 1 3) (by simp) with h281 | h281
                            · rcases p273_3 (m.d 2 3) (by simp) with h282 | h282
                              · linarith only [h265, h282, hlam]
                              · rcases p273_3 (m.d 3 4) (by simp) with h284 | h284
                                · linarith only [h266, h284, hlam]
                                · linarith only [h222, h284, hlam]
                            · linarith only [h0, h281, hlam]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [hlam, p273_0]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          rcases p273_3 (m.d 0 3) (by simp) with h289 | h289
                          · linarith only [h0, h289, hlam]
                          · linarith only [h221, h289, hlam]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [h0, h222, h265, hc01, hc12, hlam, hphi, p273_1]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [h0, h244, h265, hc01, hc12, hlam, hphi, p273_1]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [h221, hlam, p273_0]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [h265, hlam, p273_0]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [hlam, p273_0]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [h268, hlam, p273_0]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [h270, hlam, p273_0]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [h0, h265, h266, hc01, hc12, hlam, hphi, p273_1]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [h266, hlam, p273_0]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          rcases p273_3 (m.d 0 3) (by simp) with h301 | h301
                          · linarith only [h222, h301, hlam]
                          · linarith only [h221, h301, hlam]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [hlam, p273_0]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [h0, h244, h265, h266, hc01, hc12, hlam, hphi, p273_1]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [h0, h267, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p273_1, u5elo1]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [h267, hlam, p273_0]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [h267, hc23, hlam, hphi, ht34, ht45, p273_1, u5elo1]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [h272, hlam, p273_1]
                        · have p273_0 := h273c.1
                          have p273_1 := h273c.2.1
                          have p273_2 := h273c.2.2.1
                          have p273_3 := h273c.2.2.2
                          linarith only [hlam, p273_0]
                      · linarith only [h264, h272, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · linarith only [h0, h267, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h313 | h313
                · linarith only [h0, h244, h266, h313, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h313, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h221, h265, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h317 | h317
            · rcases m.htr 1 3 4 (by decide) (by decide) with h318 | h318
              · rcases m.htr 1 3 5 (by decide) (by decide) with h319 | h319
                · rcases m.htr 2 3 4 (by decide) (by decide) with h320 | h320
                  · linarith only [h221, h222, h320, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h322 | h322
                    · linarith only [h221, h244, h322, hc05, hlam, hphi, ht0b, ht5b, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h324 | h324
                      · linarith only [h0, h222, h264, h317, h318, h324, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h222, h324, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h0, h319, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h328 | h328
                · linarith only [h0, h244, h318, h328, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h328, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h221, h317, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h332 | h332
      · rcases m.htr 0 3 5 (by decide) (by decide) with h333 | h333
        · rcases m.htr 0 4 5 (by decide) (by decide) with h334 | h334
          · rcases m.htr 1 2 3 (by decide) (by decide) with h335 | h335
            · rcases m.htr 1 3 4 (by decide) (by decide) with h336 | h336
              · rcases m.htr 1 3 5 (by decide) (by decide) with h337 | h337
                · rcases m.htr 2 3 4 (by decide) (by decide) with h338 | h338
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h339 | h339
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h340 | h340
                      · linarith only [h332, h340, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h334, h340, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h221, h333, h339, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h221, h332, h338, hlam]
                · linarith only [h221, h333, h335, h337, hlam]
              · linarith only [h221, h332, h335, h336, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h347 | h347
              · rcases m.htr 1 3 5 (by decide) (by decide) with h348 | h348
                · rcases m.htr 2 3 4 (by decide) (by decide) with h349 | h349
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h350 | h350
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h351 | h351
                      · linarith only [h332, h351, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h332, h334, h351, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h0, h333, h335, h350, hlam]
                  · linarith only [h0, h332, h335, h349, hlam]
                · linarith only [h0, h333, h348, hlam]
              · linarith only [h0, h332, h347, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h358 | h358
            · rcases m.htr 1 3 4 (by decide) (by decide) with h359 | h359
              · rcases m.htr 1 3 5 (by decide) (by decide) with h360 | h360
                · rcases m.htr 2 3 4 (by decide) (by decide) with h361 | h361
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h362 | h362
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h363 | h363
                      · linarith only [h332, h334, h363, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases h3bigk with h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [hlam, p365_0]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [h0, hlam, p365_1]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [h221, hlam, p365_1]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p365_1, u0elo2]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [hc35, hlam, hphi, ht0b, ht5b, p365_1, u0elo2]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          rcases p365_3 (m.d 0 3) (by simp) with h371 | h371
                          · linarith only [h0, h371, hlam]
                          · rcases p365_3 (m.d 1 3) (by simp) with h373 | h373
                            · rcases p365_3 (m.d 2 3) (by simp) with h374 | h374
                              · linarith only [h358, h374, hlam]
                              · linarith only [h221, h374, hlam]
                            · linarith only [h0, h373, hlam]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [hlam, p365_0]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          rcases p365_3 (m.d 0 3) (by simp) with h379 | h379
                          · linarith only [h0, h379, hlam]
                          · rcases p365_3 (m.d 1 3) (by simp) with h381 | h381
                            · rcases p365_3 (m.d 2 3) (by simp) with h382 | h382
                              · linarith only [h358, h382, hlam]
                              · rcases p365_3 (m.d 3 4) (by simp) with h384 | h384
                                · linarith only [h359, h384, hlam]
                                · rcases p365_3 (m.d 3 5) (by simp) with h386 | h386
                                  · linarith only [h360, h386, hlam]
                                  · rcases h5bigk with h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [hlam, p388_0]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [hc15, hlam, hphi, ht0b, ht5b, p388_1, u0elo4]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h221, h333, h358, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p365_1, p388_1]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h221, h333, h358, h363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p365_1, p388_1]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h334, hlam, p388_1]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [hc05, hlam, hphi, p388_1, u5elo1]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [hlam, p388_0]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h362, h363, hc34, hlam, hphi, ht45, p388_1, u5elo1]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h363, hc34, hlam, hphi, ht45, p388_1, u5elo1]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h332, h334, hc34, hlam, hphi, ht45, p388_1, u5elo1]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h333, h363, hc34, hlam, hphi, ht45, p388_1, u5elo2]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h358, h362, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p365_1, p388_1]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [hlam, p388_0]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h358, h362, h363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p365_1, p388_1]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h332, h334, h358, h362, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p365_1, p388_1]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h333, hlam, p388_1]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h360, hlam, p388_1]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h362, hlam, p388_0]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [hlam, p388_0]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h363, hlam, p388_1]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h333, h363, hc34, hlam, hphi, ht45, p388_1, u5elo4]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h360, h363, hc34, hlam, hphi, ht45, p388_1, u5elo4]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [hc25, hlam, hphi, p388_1, u5elo4]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h363, hc34, hlam, hphi, ht45, p388_1, u5elo4]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [hlam, p388_0]
                            · linarith only [h358, h381, hlam]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          rcases p365_3 (m.d 0 3) (by simp) with h415 | h415
                          · linarith only [h0, h415, hlam]
                          · linarith only [h332, h415, hlam]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          rcases p365_3 (m.d 0 3) (by simp) with h418 | h418
                          · linarith only [h0, h418, hlam]
                          · linarith only [h333, h418, hlam]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [h333, h358, h363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p365_1]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [h358, hlam, p365_0]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [hlam, p365_0]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          rcases p365_3 (m.d 0 3) (by simp) with h424 | h424
                          · linarith only [h221, h424, hlam]
                          · linarith only [h332, h424, hlam]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          rcases p365_3 (m.d 0 3) (by simp) with h427 | h427
                          · linarith only [h221, h427, hlam]
                          · linarith only [h333, h427, hlam]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [h332, hlam, p365_0]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [h359, hlam, p365_0]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [h361, hlam, p365_0]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [hlam, p365_0]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [h363, hlam, p365_0]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [h333, hlam, p365_0]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [h360, hlam, p365_0]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [h362, hlam, p365_0]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [h333, hc34, hlam, hphi, ht0b, ht45, ht5b, p365_1, u0elo2]
                        · have p365_0 := h365c.1
                          have p365_1 := h365c.2.1
                          have p365_2 := h365c.2.2.1
                          have p365_3 := h365c.2.2.2
                          linarith only [hlam, p365_0]
                    · linarith only [h333, h362, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h221, h332, h333, h361, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                · linarith only [h0, h360, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h332, h359, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h444 | h444
              · rcases m.htr 1 3 5 (by decide) (by decide) with h445 | h445
                · rcases m.htr 2 3 4 (by decide) (by decide) with h446 | h446
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h447 | h447
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h448 | h448
                      · linarith only [h332, h448, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                      · rcases h3bigk with h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h0, hlam, p450_1]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h221, hlam, p450_1]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p450_1, u0elo2]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [hc35, hlam, hphi, ht0b, ht5b, p450_1, u0elo2]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          rcases p450_3 (m.d 0 3) (by simp) with h456 | h456
                          · linarith only [h0, h456, hlam]
                          · rcases p450_3 (m.d 1 3) (by simp) with h458 | h458
                            · rcases p450_3 (m.d 2 3) (by simp) with h459 | h459
                              · rcases p450_3 (m.d 3 4) (by simp) with h460 | h460
                                · linarith only [h444, h460, hlam]
                                · rcases p450_3 (m.d 3 5) (by simp) with h462 | h462
                                  · linarith only [h445, h462, hlam]
                                  · rcases h5bigk with h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [hlam, p464_0]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [h445, h448, hc34, hlam, hphi, ht0b, ht45, ht5b, p464_1, u0elo4]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [h333, h358, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p450_1, p464_1]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [h333, h358, h448, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p450_1, p464_1]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [h334, hlam, p464_1]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [hc05, hlam, hphi, p464_1, u5elo1]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [hlam, p464_0]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [h447, h448, hc34, hlam, hphi, ht45, p464_1, u5elo1]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [h448, hc34, hlam, hphi, ht45, p464_1, u5elo1]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [h332, h334, hc34, hlam, hphi, ht45, p464_1, u5elo1]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [h333, h448, hc34, hlam, hphi, ht45, p464_1, u5elo2]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [hc15, hlam, hphi, p464_1, u5elo2]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [hlam, p464_0]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [h448, hc34, hlam, hphi, ht45, p464_1, u5elo2]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [h332, h334, hc34, hlam, hphi, ht45, p464_1, u5elo2]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [h333, hlam, p464_1]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [h445, hlam, p464_1]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [h447, hlam, p464_0]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [hlam, p464_0]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [h448, hlam, p464_1]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [h333, h448, hc34, hlam, hphi, ht45, p464_1, u5elo4]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [h445, h448, hc34, hlam, hphi, ht45, p464_1, u5elo4]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [hc25, hlam, hphi, p464_1, u5elo4]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [h448, hc34, hlam, hphi, ht45, p464_1, u5elo4]
                                    · have p464_0 := h464c.1
                                      have p464_1 := h464c.2.1
                                      have p464_2 := h464c.2.2.1
                                      have p464_3 := h464c.2.2.2
                                      linarith only [hlam, p464_0]
                              · linarith only [h221, h459, hlam]
                            · linarith only [h0, h458, hlam]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h358, hlam, p450_1]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          rcases p450_3 (m.d 0 3) (by simp) with h494 | h494
                          · linarith only [h0, h494, hlam]
                          · linarith only [h332, h494, hlam]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          rcases p450_3 (m.d 0 3) (by simp) with h497 | h497
                          · linarith only [h0, h497, hlam]
                          · linarith only [h333, h497, hlam]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          rcases p450_3 (m.d 0 3) (by simp) with h500 | h500
                          · linarith only [h221, h500, hlam]
                          · rcases p450_3 (m.d 1 3) (by simp) with h502 | h502
                            · linarith only [h358, h502, hlam]
                            · linarith only [h0, h502, hlam]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p450_1]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          rcases p450_3 (m.d 0 3) (by simp) with h507 | h507
                          · linarith only [h221, h507, hlam]
                          · linarith only [h332, h507, hlam]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          rcases p450_3 (m.d 0 3) (by simp) with h510 | h510
                          · linarith only [h221, h510, hlam]
                          · linarith only [h333, h510, hlam]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h332, hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h444, hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h446, hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h448, hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h333, hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h445, hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h447, hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h333, hc34, hlam, hphi, ht0b, ht45, ht5b, p450_1, u0elo2]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [hlam, p450_0]
                    · linarith only [h333, h447, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h332, h358, h446, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h0, h333, h445, hlam]
              · linarith only [h0, h332, h444, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
        · linarith only [h332, h333, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h528 | h528
        · rcases m.htr 0 4 5 (by decide) (by decide) with h529 | h529
          · rcases m.htr 1 2 3 (by decide) (by decide) with h530 | h530
            · rcases m.htr 1 3 4 (by decide) (by decide) with h531 | h531
              · rcases m.htr 1 3 5 (by decide) (by decide) with h532 | h532
                · rcases m.htr 2 3 4 (by decide) (by decide) with h533 | h533
                  · linarith only [h332, h528, h530, h533, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h535 | h535
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h536 | h536
                      · rcases h3bigk with h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [hlam, p537_0]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [h0, hlam, p537_1]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [h221, hlam, p537_1]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [h332, hlam, p537_0]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [h536, hc45, hlam, hphi, ht0b, ht5b, p537_1, u0elo2]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          rcases p537_3 (m.d 0 3) (by simp) with h543 | h543
                          · linarith only [h0, h543, hlam]
                          · rcases p537_3 (m.d 1 3) (by simp) with h545 | h545
                            · rcases p537_3 (m.d 2 3) (by simp) with h546 | h546
                              · linarith only [h530, h546, hlam]
                              · linarith only [h221, h546, hlam]
                            · linarith only [h0, h545, hlam]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [hlam, p537_0]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          rcases p537_3 (m.d 0 3) (by simp) with h551 | h551
                          · linarith only [h0, h551, hlam]
                          · rcases p537_3 (m.d 1 3) (by simp) with h553 | h553
                            · rcases p537_3 (m.d 2 3) (by simp) with h554 | h554
                              · linarith only [h530, h554, hlam]
                              · rcases p537_3 (m.d 3 4) (by simp) with h556 | h556
                                · linarith only [h531, h556, hlam]
                                · linarith only [h533, h556, hlam]
                            · linarith only [h530, h553, hlam]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [h221, h533, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p537_1]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [h221, h528, h531, h533, hlam, p537_2]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [h531, h533, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p537_1]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [h530, hlam, p537_0]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [hlam, p537_0]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [h533, hlam, p537_0]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [h530, h531, h533, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p537_1]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [h528, h530, h531, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p537_1]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [h531, hlam, p537_0]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [h221, h530, h531, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p537_1]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [hlam, p537_0]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          rcases p537_3 (m.d 0 3) (by simp) with h571 | h571
                          · linarith only [h332, h571, hlam]
                          · linarith only [h528, h571, hlam]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [h528, hlam, p537_0]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [h532, hlam, p537_0]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [h535, hlam, p537_0]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [h536, hlam, p537_1]
                        · have p537_0 := h537c.1
                          have p537_1 := h537c.2.1
                          have p537_2 := h537c.2.2.1
                          have p537_3 := h537c.2.2.2
                          linarith only [hlam, p537_0]
                      · linarith only [h332, h536, hc03, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h221, h528, h535, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h332, h528, h531, h532, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h582 | h582
                · rcases m.htr 2 3 4 (by decide) (by decide) with h583 | h583
                  · linarith only [h0, h530, h531, h583, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h585 | h585
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h586 | h586
                      · rcases h3bigk with h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h0, hlam, p587_1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h221, hlam, p587_1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h332, hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h586, hc45, hlam, hphi, ht0b, ht5b, p587_1, u0elo2]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h531, hc03, hc34, hlam, hphi, p587_1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h531, hc23, hc34, hlam, hphi, p587_1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h531, hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          rcases p587_3 (m.d 0 3) (by simp) with h597 | h597
                          · linarith only [h0, h597, hlam]
                          · linarith only [h528, h597, hlam]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h528, h530, h586, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p587_1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h530, hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h583, hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          rcases p587_3 (m.d 0 3) (by simp) with h604 | h604
                          · linarith only [h221, h604, hlam]
                          · linarith only [h528, h604, hlam]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          rcases p587_3 (m.d 0 3) (by simp) with h607 | h607
                          · linarith only [h607, hlam, p587_0]
                          · rcases p587_3 (m.d 1 3) (by simp) with h609 | h609
                            · linarith only [h531, h609, hlam]
                            · linarith only [h0, h609, hlam]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p587_1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h221, hc02, hc34, hlam, hphi, ht23, p587_1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          rcases p587_3 (m.d 0 3) (by simp) with h615 | h615
                          · linarith only [h332, h615, hlam]
                          · linarith only [h528, h615, hlam]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h528, hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h582, hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h585, hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h586, hlam, p587_1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [hlam, p587_0]
                      · linarith only [h332, h528, h586, hc35, hlam, hphi, u5elo4]
                    · linarith only [h221, h528, h585, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h221, h528, h530, h582, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h626 | h626
              · rcases m.htr 1 3 5 (by decide) (by decide) with h627 | h627
                · rcases m.htr 2 3 4 (by decide) (by decide) with h628 | h628
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h629 | h629
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h630 | h630
                      · rcases h3bigk with h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [hlam, p631_0]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [h0, hlam, p631_1]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [h221, hlam, p631_1]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [h332, hlam, p631_0]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [h332, h530, h626, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p631_1]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          rcases p631_3 (m.d 0 3) (by simp) with h637 | h637
                          · linarith only [h0, h637, hlam]
                          · rcases p631_3 (m.d 1 3) (by simp) with h639 | h639
                            · rcases p631_3 (m.d 2 3) (by simp) with h640 | h640
                              · rcases p631_3 (m.d 3 4) (by simp) with h641 | h641
                                · linarith only [h626, h641, hlam]
                                · linarith only [h332, h641, hlam]
                              · linarith only [h221, h640, hlam]
                            · linarith only [h0, h639, hlam]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [hlam, p631_0]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [h530, hlam, p631_1]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [h0, h332, h530, hc01, hc23, hlam, hphi, ht12, p631_1]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [h332, h528, h626, hlam, p631_2]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          rcases p631_3 (m.d 0 3) (by simp) with h650 | h650
                          · linarith only [h221, h650, hlam]
                          · rcases p631_3 (m.d 1 3) (by simp) with h652 | h652
                            · linarith only [h530, h652, hlam]
                            · linarith only [h0, h652, hlam]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [h332, h528, h626, h630, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p631_1]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [hlam, p631_0]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [h332, h528, h630, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p631_1]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [h332, h528, h530, h626, hlam, p631_2]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [h528, h626, h630, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p631_1]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [h626, hlam, p631_0]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [h628, hlam, p631_0]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [hlam, p631_0]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          rcases p631_3 (m.d 0 3) (by simp) with h663 | h663
                          · linarith only [h332, h663, hlam]
                          · linarith only [h528, h663, hlam]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [h528, hlam, p631_0]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [h627, hlam, p631_0]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [h629, hlam, p631_0]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [h630, hlam, p631_1]
                        · have p631_0 := h631c.1
                          have p631_1 := h631c.2.1
                          have p631_2 := h631c.2.2.1
                          have p631_3 := h631c.2.2.2
                          linarith only [hlam, p631_0]
                      · linarith only [h332, h528, h630, hc35, hlam, hphi, u5elo4]
                    · linarith only [h528, h530, h629, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h530, h626, h628, hlam]
                · linarith only [h332, h528, h626, h627, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h675 | h675
                · rcases m.htr 2 3 4 (by decide) (by decide) with h676 | h676
                  · linarith only [h0, h626, h676, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h678 | h678
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h679 | h679
                      · rcases h3bigk with h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h0, hlam, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h221, hlam, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h332, hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h679, hc45, hlam, hphi, ht0b, ht5b, p680_1, u0elo2]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h530, h676, hc03, hc34, hlam, hphi, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h530, hlam, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h626, hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          rcases p680_3 (m.d 0 3) (by simp) with h690 | h690
                          · linarith only [h0, h690, hlam]
                          · linarith only [h528, h690, hlam]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h528, h676, h679, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h676, hc13, hc34, hlam, hphi, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h676, hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          rcases p680_3 (m.d 0 3) (by simp) with h697 | h697
                          · linarith only [h221, h697, hlam]
                          · linarith only [h528, h697, hlam]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          rcases p680_3 (m.d 0 3) (by simp) with h700 | h700
                          · linarith only [h700, hlam, p680_0]
                          · rcases p680_3 (m.d 1 3) (by simp) with h702 | h702
                            · linarith only [h626, h702, hlam]
                            · linarith only [h0, h702, hlam]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h221, hc02, hc34, hlam, hphi, ht23, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          rcases p680_3 (m.d 0 3) (by simp) with h708 | h708
                          · linarith only [h332, h708, hlam]
                          · linarith only [h528, h708, hlam]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h528, hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h675, hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h678, hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h679, hlam, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [hlam, p680_0]
                      · linarith only [h332, h528, h679, hc35, hlam, hphi, u5elo4]
                    · linarith only [h0, h528, h530, h678, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h528, h675, hlam]
          · linarith only [h332, h528, h529, hc35, hlam, hphi, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h720 | h720
          · rcases m.htr 1 2 3 (by decide) (by decide) with h721 | h721
            · rcases m.htr 1 3 4 (by decide) (by decide) with h722 | h722
              · rcases m.htr 1 3 5 (by decide) (by decide) with h723 | h723
                · rcases m.htr 2 3 4 (by decide) (by decide) with h724 | h724
                  · linarith only [h0, h332, h721, h724, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h726 | h726
                    · linarith only [h0, h528, h722, h724, h726, hc01, hc13, hlam, hphi]
                    · linarith only [h221, h723, h726, hc02, hlam, hphi, ht23, ht34, ht45, u5elo1]
                · linarith only [h722, h723, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h730 | h730
                · linarith only [h0, h528, h722, h730, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h730, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h733 | h733
              · rcases m.htr 1 3 5 (by decide) (by decide) with h734 | h734
                · rcases m.htr 2 3 4 (by decide) (by decide) with h735 | h735
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h736 | h736
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h737 | h737
                      · rcases h3bigk with h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [hlam, p738_0]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h0, hlam, p738_1]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h221, hlam, p738_1]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h332, hlam, p738_0]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h528, hlam, p738_0]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          rcases p738_3 (m.d 0 3) (by simp) with h744 | h744
                          · linarith only [h0, h744, hlam]
                          · rcases p738_3 (m.d 1 3) (by simp) with h746 | h746
                            · rcases p738_3 (m.d 2 3) (by simp) with h747 | h747
                              · rcases p738_3 (m.d 3 4) (by simp) with h748 | h748
                                · linarith only [h733, h748, hlam]
                                · linarith only [h332, h748, hlam]
                              · linarith only [h221, h747, hlam]
                            · linarith only [h0, h746, hlam]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [hlam, p738_0]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h721, hlam, p738_1]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h0, h528, h737, hc01, hc13, hlam, hphi, p738_1]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h0, h528, h721, hc01, hc23, hlam, hphi, ht12, p738_1]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          rcases p738_3 (m.d 0 3) (by simp) with h757 | h757
                          · linarith only [h221, h757, hlam]
                          · rcases p738_3 (m.d 1 3) (by simp) with h759 | h759
                            · linarith only [h721, h759, hlam]
                            · linarith only [h0, h759, hlam]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p738_1]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [hlam, p738_0]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h0, h528, h737, hc01, hc23, hlam, hphi, ht12, p738_1]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h0, h528, hc01, hc23, hlam, hphi, ht12, p738_1]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h0, h733, hc01, hc13, hlam, hphi, p738_1]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h733, hlam, p738_0]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h735, hlam, p738_0]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [hlam, p738_0]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h0, h528, h721, h733, hc01, hc23, hlam, hphi, ht12, p738_1]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h0, h736, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p738_1, u5elo2]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h734, hlam, p738_0]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h736, hlam, p738_0]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [h737, hlam, p738_1]
                        · have p738_0 := h738c.1
                          have p738_1 := h738c.2.1
                          have p738_2 := h738c.2.2.1
                          have p738_3 := h738c.2.2.2
                          linarith only [hlam, p738_0]
                      · linarith only [h720, h737, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h721, h736, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h721, h733, h735, hlam]
                · linarith only [h0, h332, h733, h734, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h780 | h780
                · linarith only [h0, h528, h733, h780, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h780, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h783 | h783
            · rcases m.htr 1 3 4 (by decide) (by decide) with h784 | h784
              · rcases m.htr 1 3 5 (by decide) (by decide) with h785 | h785
                · rcases m.htr 2 3 4 (by decide) (by decide) with h786 | h786
                  · linarith only [h0, h332, h783, h786, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h788 | h788
                    · linarith only [h0, h528, h783, h784, h786, h788, hc01, hc12, hlam, hphi]
                    · linarith only [h221, h788, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h784, h785, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h792 | h792
                · linarith only [h0, h528, h784, h792, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h792, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h795 | h795
              · rcases m.htr 1 3 5 (by decide) (by decide) with h796 | h796
                · rcases m.htr 2 3 4 (by decide) (by decide) with h797 | h797
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h798 | h798
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h799 | h799
                      · linarith only [h0, h332, h720, h795, h799, hc01, hc13, hlam, hphi]
                      · linarith only [h0, h332, h799, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · linarith only [h783, h796, h798, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
                  · linarith only [h783, h795, h797, hlam]
                · linarith only [h0, h332, h795, h796, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h805 | h805
                · linarith only [h0, h528, h795, h805, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h805, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]

theorem n7l_sBT3_M_IR_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · linarith only [h11, h12, hc34, hlam, hphi, ht45, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                          · linarith only [h0, h11, h15, h3, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                            · linarith only [h0, h17, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · linarith only [h11, h17, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h10, h6, h9, hc34, hlam, hphi, ht45, u5elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                      · linarith only [h0, h21, h3, h5, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                        · linarith only [h21, h23, h6, h7, hc34, hlam, hphi, ht45, u5elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                          · linarith only [h21, h25, h7, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                            · rcases h3bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                rcases p28_3 (m.d 0 3) (by simp) with h30 | h30
                                · rcases p28_3 (m.d 1 3) (by simp) with h31 | h31
                                  · linarith only [h1, h31, hlam]
                                  · rcases p28_3 (m.d 2 3) (by simp) with h33 | h33
                                    · linarith only [h3, h33, hlam]
                                    · rcases p28_3 (m.d 3 4) (by simp) with h35 | h35
                                      · linarith only [h35, h5, hlam]
                                      · linarith only [h35, h9, hlam]
                                · linarith only [h1, h30, hlam]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                rcases p28_3 (m.d 0 3) (by simp) with h39 | h39
                                · rcases p28_3 (m.d 1 3) (by simp) with h40 | h40
                                  · linarith only [h1, h40, hlam]
                                  · linarith only [h40, h7, hlam]
                                · linarith only [h3, h39, hlam]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h0, h27, h3, hc01, hlam, hphi, ht0b, ht5b, p28_1, u5ehi9]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                rcases p28_3 (m.d 0 3) (by simp) with h45 | h45
                                · rcases p28_3 (m.d 1 3) (by simp) with h46 | h46
                                  · linarith only [h1, h46, hlam]
                                  · rcases p28_3 (m.d 2 3) (by simp) with h48 | h48
                                    · linarith only [h3, h48, hlam]
                                    · rcases p28_3 (m.d 3 4) (by simp) with h50 | h50
                                      · linarith only [h5, h50, hlam]
                                      · linarith only [h27, h50, hlam]
                                · linarith only [h45, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h1, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h21, hc23, hc35, hlam, hphi, p28_1]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h9, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h21, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h3, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h7, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h23, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h25, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h5, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                rcases p28_3 (m.d 0 3) (by simp) with h65 | h65
                                · rcases p28_3 (m.d 1 3) (by simp) with h66 | h66
                                  · linarith only [h66, hlam, p28_0]
                                  · rcases p28_3 (m.d 2 3) (by simp) with h68 | h68
                                    · linarith only [h23, h68, hlam]
                                    · rcases p28_3 (m.d 3 4) (by simp) with h70 | h70
                                      · rcases p28_3 (m.d 3 5) (by simp) with h71 | h71
                                        · linarith only [h27, h71, hlam]
                                        · linarith only [h21, h71, hlam]
                                      · linarith only [h70, hlam, p28_0]
                                · linarith only [h1, h65, hlam]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                rcases p28_3 (m.d 0 3) (by simp) with h76 | h76
                                · rcases p28_3 (m.d 1 3) (by simp) with h77 | h77
                                  · linarith only [h77, h9, hlam]
                                  · linarith only [h7, h77, hlam]
                                · linarith only [h3, h76, hlam]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h0, h21, h3, h5, hc01, hlam, hphi, ht0b, ht5b, p28_1, u5ehi6]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h6, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [hc13, hlam, hphi, ht34, ht45, p28_1, u5elo3]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h6, hc23, hlam, hphi, ht34, ht45, p28_1, u5elo0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h27, hlam, p28_1]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [hlam, p28_0]
                            · linarith only [h27, h7, h9, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h4, h7, h8, hc23, hlam, hphi, ht34, ht45, u5elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h90 | h90
                  · linarith only [h0, h3, h7, h90, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h92 | h92
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h93 | h93
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h96 | h96
                            · linarith only [h1, h92, h96, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · rcases h3bigk with h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h0, h3, h93, hc01, hlam, hphi, ht0b, ht5b, p98_1, u5ehi8]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h0, h3, h7, h93, hc01, hlam, hphi, ht0b, ht5b, p98_1, u5ehi8]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                rcases p98_3 (m.d 0 3) (by simp) with h102 | h102
                                · rcases p98_3 (m.d 1 3) (by simp) with h103 | h103
                                  · linarith only [h1, h103, hlam]
                                  · linarith only [h103, h92, hlam]
                                · linarith only [h102, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                rcases p98_3 (m.d 0 3) (by simp) with h107 | h107
                                · rcases p98_3 (m.d 1 3) (by simp) with h108 | h108
                                  · linarith only [h1, h108, hlam]
                                  · linarith only [h108, h93, hlam]
                                · linarith only [h107, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h1, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h7, hlam, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                rcases p98_3 (m.d 0 3) (by simp) with h115 | h115
                                · rcases p98_3 (m.d 1 3) (by simp) with h116 | h116
                                  · rcases p98_3 (m.d 2 3) (by simp) with h117 | h117
                                    · rcases p98_3 (m.d 3 4) (by simp) with h118 | h118
                                      · linarith only [h118, hlam, p98_0]
                                      · rcases p98_3 (m.d 3 5) (by simp) with h120 | h120
                                        · linarith only [h120, h93, hlam]
                                        · linarith only [h120, h96, hlam]
                                    · linarith only [h117, h94, hlam]
                                  · linarith only [h116, hlam, p98_0]
                                · linarith only [h115, h5, hlam]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p98_1, u5ehi8]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h3, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h0, h3, h92, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                rcases p98_3 (m.d 0 3) (by simp) with h130 | h130
                                · rcases p98_3 (m.d 1 3) (by simp) with h131 | h131
                                  · linarith only [h131, h7, hlam]
                                  · linarith only [h131, h92, hlam]
                                · linarith only [h130, h5, hlam]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p98_1, u5ehi8]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h5, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h92, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h94, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h96, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h6, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h93, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h95, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hc34, hlam, hphi, ht45, p98_1, u5elo3]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                          · linarith only [h7, h93, h95, hlam]
                        · linarith only [h0, h3, h5, h7, h93, h94, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · linarith only [h92, h93, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h149 | h149
                      · linarith only [h0, h149, h3, h5, h92, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h151 | h151
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h152 | h152
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h153 | h153
                            · linarith only [h0, h151, h153, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · linarith only [h153, h7, h92, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h152, h6, h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h157 | h157
                          · linarith only [h0, h151, h157, h3, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · linarith only [h157, h6, h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
              · linarith only [h6, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h161 | h161
              · rcases m.htr 1 2 3 (by decide) (by decide) with h162 | h162
                · rcases m.htr 1 2 5 (by decide) (by decide) with h163 | h163
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h164 | h164
                    · linarith only [h161, h164, h5, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h166 | h166
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h167 | h167
                        · linarith only [h1, h166, h167, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h169 | h169
                          · linarith only [h0, h162, h169, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · linarith only [h1, h166, h169, h5, hc23, hc34, hlam, hphi]
                      · linarith only [h161, h166, h5, hc13, hc34, hlam, hphi]
                  · linarith only [h162, h163, h4, hc23, hlam, hphi, ht34, ht45, u5elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h174 | h174
                  · linarith only [h0, h162, h174, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h176 | h176
                    · linarith only [h161, h176, h5, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h178 | h178
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h179 | h179
                        · linarith only [h179, h3, h5, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h181 | h181
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h182 | h182
                            · rcases h3bigk with h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [hlam, p183_0]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h178, h182, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p183_1, u5ehi9]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h162, h178, h182, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p183_1, u5ehi9]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h5, hlam, p183_0]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h182, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p183_1, u5ehi9]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h1, hlam, p183_0]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [hlam, p183_0]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h162, hlam, p183_1]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h176, hlam, p183_0]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h1, h182, hc01, hlam, hphi, ht0b, ht5b, p183_1, u5ehi9]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h3, hlam, p183_0]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h3, h5, hc13, hc34, hlam, hphi, p183_1]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [hlam, p183_0]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h179, hlam, p183_0]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h182, h3, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p183_1, u5ehi9]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p183_1, u0ehi2]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h178, h182, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p183_1, u5ehi9]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h162, h178, h182, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p183_1, u5ehi9]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [hlam, p183_0]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                rcases p183_3 (m.d 0 3) (by simp) with h203 | h203
                                · linarith only [h203, h5, hlam]
                                · linarith only [h161, h203, hlam]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h161, hlam, p183_0]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h178, hlam, p183_0]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h181, hlam, p183_0]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [h182, hlam, p183_1]
                              · have p183_0 := h183c.1
                                have p183_1 := h183c.2.1
                                have p183_2 := h183c.2.2.1
                                have p183_3 := h183c.2.2.2
                                linarith only [hlam, p183_0]
                            · linarith only [h182, h5, hc03, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h162, h178, h181, hlam]
                      · linarith only [h161, h178, h5, hc13, hc34, hlam, hphi]
              · linarith only [h161, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h216 | h216
          · rcases m.htr 0 3 4 (by decide) (by decide) with h217 | h217
            · rcases m.htr 0 3 5 (by decide) (by decide) with h218 | h218
              · rcases m.htr 1 2 3 (by decide) (by decide) with h219 | h219
                · linarith only [h216, h219, h3, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h221 | h221
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h222 | h222
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h223 | h223
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h224 | h224
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h225 | h225
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h226 | h226
                            · linarith only [h1, h222, h226, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · rcases h3bigk with h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h219, h221, h225, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p228_1, u5ehi8]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h3, hlam, p228_1]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                rcases p228_3 (m.d 0 3) (by simp) with h232 | h232
                                · rcases p228_3 (m.d 1 3) (by simp) with h233 | h233
                                  · linarith only [h1, h233, hlam]
                                  · linarith only [h222, h233, hlam]
                                · linarith only [h232, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                rcases p228_3 (m.d 0 3) (by simp) with h237 | h237
                                · rcases p228_3 (m.d 1 3) (by simp) with h238 | h238
                                  · linarith only [h1, h238, hlam]
                                  · linarith only [h223, h238, hlam]
                                · linarith only [h237, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h1, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h219, hlam, p228_1]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                rcases p228_3 (m.d 0 3) (by simp) with h245 | h245
                                · rcases p228_3 (m.d 1 3) (by simp) with h246 | h246
                                  · rcases p228_3 (m.d 2 3) (by simp) with h247 | h247
                                    · rcases p228_3 (m.d 3 4) (by simp) with h248 | h248
                                      · linarith only [h248, hlam, p228_0]
                                      · rcases p228_3 (m.d 3 5) (by simp) with h250 | h250
                                        · linarith only [h223, h250, hlam]
                                        · linarith only [h226, h250, hlam]
                                    · linarith only [h224, h247, hlam]
                                  · linarith only [h246, hlam, p228_0]
                                · linarith only [h217, h245, hlam]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p228_1, u5ehi8]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p228_1, u0ehi2]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h219, h221, h225, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p228_1, u5ehi8]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                rcases p228_3 (m.d 0 3) (by simp) with h260 | h260
                                · linarith only [h260, h3, hlam]
                                · linarith only [h217, h260, hlam]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                rcases p228_3 (m.d 0 3) (by simp) with h263 | h263
                                · linarith only [h263, h3, hlam]
                                · linarith only [h218, h263, hlam]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h217, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h222, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h224, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h226, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h218, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h223, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h225, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h221, h225, hc34, hlam, hphi, ht45, p228_1, u5elo1]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [hlam, p228_0]
                          · linarith only [h0, h1, h221, h223, h225, h3, hc03, hlam, hphi, ht0b, ht5b, u5ehi7]
                        · linarith only [h0, h221, h224, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h218, h222, h223, hc34, hlam, hphi, ht45, u5elo0]
                    · linarith only [h217, h219, h221, h222, hc03, hlam, hphi, ht0b, ht5b, u5ehi7]
                  · linarith only [h216, h221, h3, hc12, hc23, hlam, hphi]
              · linarith only [h218, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h282 | h282
              · rcases m.htr 1 2 3 (by decide) (by decide) with h283 | h283
                · linarith only [h216, h283, h3, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h285 | h285
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h286 | h286
                    · linarith only [h217, h282, h286, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h288 | h288
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h289 | h289
                        · linarith only [h0, h217, h285, h289, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                        · linarith only [h0, h285, h289, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h217, h282, h288, hc13, hc34, hlam, hphi]
                  · linarith only [h216, h217, h285, h3, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h216, h282, h3, hlam, hphi, u5ehi7, u5elo3]
          · linarith only [h216, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h296 | h296
        · rcases m.htr 0 2 5 (by decide) (by decide) with h297 | h297
          · rcases m.htr 0 3 4 (by decide) (by decide) with h298 | h298
            · linarith only [h0, h2, h296, h298, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h300 | h300
              · rcases m.htr 1 2 3 (by decide) (by decide) with h301 | h301
                · rcases m.htr 1 2 5 (by decide) (by decide) with h302 | h302
                  · linarith only [h0, h2, h302, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                  · linarith only [h301, h302, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h305 | h305
                  · linarith only [h0, h2, h296, h301, h305, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h307 | h307
                    · linarith only [h298, h307, hc13, hlam, hphi, ht01, u0ehi2]
                    · linarith only [h0, h2, h296, h301, h307, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h300, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
          · linarith only [h296, h297, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h312 | h312
          · rcases m.htr 0 3 4 (by decide) (by decide) with h313 | h313
            · linarith only [h1, h2, h313, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h315 | h315
              · rcases m.htr 1 2 3 (by decide) (by decide) with h316 | h316
                · linarith only [h296, h312, h316, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h318 | h318
                  · linarith only [h1, h2, h316, h318, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                  · linarith only [h296, h312, h318, hc12, hc23, hlam, hphi]
              · linarith only [h296, h312, h315, hlam, hphi, u5ehi7, u5elo3]
          · linarith only [h312, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h323 | h323
      · rcases m.htr 0 2 3 (by decide) (by decide) with h324 | h324
        · linarith only [h0, h1, h324, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h326 | h326
          · rcases m.htr 0 3 4 (by decide) (by decide) with h327 | h327
            · rcases m.htr 0 3 5 (by decide) (by decide) with h328 | h328
              · rcases m.htr 1 2 3 (by decide) (by decide) with h329 | h329
                · linarith only [h324, h326, h329, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h331 | h331
                  · linarith only [h0, h1, h329, h331, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                  · linarith only [h0, h1, h326, h329, h331, hc12, hc23, hlam, hphi]
              · linarith only [h1, h323, h328, hc14, hlam, hphi, ht45, u5elo3]
            · linarith only [h1, h323, h327, hlam]
          · linarith only [h326, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h337 | h337
        · linarith only [h0, h1, h337, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h339 | h339
          · rcases m.htr 0 3 4 (by decide) (by decide) with h340 | h340
            · rcases m.htr 0 3 5 (by decide) (by decide) with h341 | h341
              · rcases m.htr 1 2 3 (by decide) (by decide) with h342 | h342
                · linarith only [h337, h339, h342, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h344 | h344
                  · linarith only [h0, h1, h344, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                  · linarith only [h0, h1, h339, h342, h344, hc12, hc23, hlam, hphi]
              · linarith only [h0, h323, h339, h340, h341, hlam, hphi, u5ehi7, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h348 | h348
              · rcases m.htr 1 2 3 (by decide) (by decide) with h349 | h349
                · linarith only [h0, h1, h340, h349, hc23, hc34, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h351 | h351
                  · linarith only [h0, h1, h340, h351, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                  · linarith only [h0, h1, h339, h340, h351, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h0, h1, h339, h348, hlam, hphi, u5ehi7, u5elo3]
          · linarith only [h339, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h356 | h356
    · rcases m.htr 0 1 4 (by decide) (by decide) with h357 | h357
      · rcases m.htr 0 2 3 (by decide) (by decide) with h358 | h358
        · rcases m.htr 0 2 5 (by decide) (by decide) with h359 | h359
          · rcases m.htr 0 3 4 (by decide) (by decide) with h360 | h360
            · rcases m.htr 0 3 5 (by decide) (by decide) with h361 | h361
              · rcases m.htr 1 2 3 (by decide) (by decide) with h362 | h362
                · rcases m.htr 1 2 5 (by decide) (by decide) with h363 | h363
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h364 | h364
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h365 | h365
                      · linarith only [h0, h356, h365, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                      · linarith only [h364, h365, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h368 | h368
                      · linarith only [h0, h356, h360, h364, h368, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h370 | h370
                        · linarith only [h362, h364, h370, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h372 | h372
                          · linarith only [h0, h356, h360, h362, h364, h368, h372, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi6]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h374 | h374
                            · linarith only [h0, h356, h360, h374, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                            · linarith only [h362, h364, h374, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h0, h363, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h0, h356, h360, h362, hc23, hlam, hphi, ht01, ht12, u0ehi3]
              · linarith only [h360, h361, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h380 | h380
              · rcases m.htr 1 2 3 (by decide) (by decide) with h381 | h381
                · rcases m.htr 1 2 5 (by decide) (by decide) with h382 | h382
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h383 | h383
                    · linarith only [h360, h380, h383, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h385 | h385
                      · linarith only [h0, h357, h383, h385, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                      · linarith only [h360, h380, h381, h385, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h357, h359, h382, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h357, h360, h380, h381, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
              · linarith only [h380, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
          · linarith only [h359, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
        · linarith only [h0, h356, h358, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h393 | h393
        · rcases m.htr 0 2 5 (by decide) (by decide) with h394 | h394
          · rcases m.htr 0 3 4 (by decide) (by decide) with h395 | h395
            · linarith only [h356, h357, h395, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h397 | h397
              · rcases m.htr 1 2 3 (by decide) (by decide) with h398 | h398
                · rcases m.htr 1 2 5 (by decide) (by decide) with h399 | h399
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h400 | h400
                    · linarith only [h356, h395, h397, h400, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h402 | h402
                      · linarith only [h356, h357, h400, h402, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                      · linarith only [h356, h357, h397, h398, h400, h402, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h394, h399, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo0]
                · linarith only [h0, h356, h397, h398, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
              · linarith only [h397, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
          · linarith only [h0, h356, h394, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo2]
        · linarith only [h0, h356, h393, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h410 | h410
      · rcases m.htr 0 2 3 (by decide) (by decide) with h411 | h411
        · rcases m.htr 0 2 5 (by decide) (by decide) with h412 | h412
          · rcases m.htr 0 3 4 (by decide) (by decide) with h413 | h413
            · rcases m.htr 0 3 5 (by decide) (by decide) with h414 | h414
              · rcases m.htr 1 2 3 (by decide) (by decide) with h415 | h415
                · rcases m.htr 1 2 5 (by decide) (by decide) with h416 | h416
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h417 | h417
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h418 | h418
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h419 | h419
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h420 | h420
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h421 | h421
                            · linarith only [h411, h419, h421, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · rcases h3bigk with h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h356, hlam, p423_1]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h0, h411, h420, hc12, hlam, hphi, ht01, ht0b, ht5b, p423_1, u5ehi8]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                rcases p423_3 (m.d 0 3) (by simp) with h427 | h427
                                · rcases p423_3 (m.d 1 3) (by simp) with h428 | h428
                                  · rcases p423_3 (m.d 2 3) (by simp) with h429 | h429
                                    · linarith only [h411, h429, hlam]
                                    · linarith only [h419, h429, hlam]
                                  · linarith only [h417, h428, hlam]
                                · linarith only [h427, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                rcases p423_3 (m.d 0 3) (by simp) with h434 | h434
                                · rcases p423_3 (m.d 1 3) (by simp) with h435 | h435
                                  · rcases p423_3 (m.d 2 3) (by simp) with h436 | h436
                                    · linarith only [h411, h436, hlam]
                                    · linarith only [h420, h436, hlam]
                                  · linarith only [h418, h435, hlam]
                                · linarith only [h434, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h415, hc12, hlam, hphi, ht01, p423_1, u0ehi2]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h415, h420, hc12, hlam, hphi, ht01, ht0b, ht5b, p423_1, u5ehi8]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                rcases p423_3 (m.d 0 3) (by simp) with h444 | h444
                                · linarith only [h356, h444, hlam]
                                · linarith only [h413, h444, hlam]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                rcases p423_3 (m.d 0 3) (by simp) with h447 | h447
                                · linarith only [h356, h447, hlam]
                                · linarith only [h414, h447, hlam]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h411, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h415, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                rcases p423_3 (m.d 0 3) (by simp) with h453 | h453
                                · rcases p423_3 (m.d 1 3) (by simp) with h454 | h454
                                  · rcases p423_3 (m.d 2 3) (by simp) with h455 | h455
                                    · rcases p423_3 (m.d 3 4) (by simp) with h456 | h456
                                      · linarith only [h456, hlam, p423_0]
                                      · rcases p423_3 (m.d 3 5) (by simp) with h458 | h458
                                        · linarith only [h420, h458, hlam]
                                        · linarith only [h421, h458, hlam]
                                    · linarith only [h455, hlam, p423_0]
                                  · linarith only [h417, h454, hlam]
                                · linarith only [h413, h453, hlam]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h0, h411, hc12, hlam, hphi, ht01, ht0b, ht5b, p423_1, u5ehi8]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h413, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h417, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h419, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h421, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h414, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h418, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h420, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h420, hc34, hlam, hphi, ht45, p423_1, u5elo2]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [hlam, p423_0]
                          · linarith only [h419, h420, hc34, hlam, hphi, ht45, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h476 | h476
                          · linarith only [h356, h410, h415, h417, h419, h476, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h478 | h478
                            · linarith only [h356, h410, h415, h417, h478, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                            · linarith only [h419, h478, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h356, h418, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                    · linarith only [h356, h410, h417, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                  · linarith only [h0, h416, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
                · linarith only [h0, h410, h415, hc23, hlam, hphi, ht01, ht12, u0ehi3]
              · linarith only [h414, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
            · linarith only [h356, h410, h413, hlam]
          · linarith only [h411, h412, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h488 | h488
          · rcases m.htr 0 3 4 (by decide) (by decide) with h489 | h489
            · rcases m.htr 0 3 5 (by decide) (by decide) with h490 | h490
              · rcases m.htr 1 2 3 (by decide) (by decide) with h491 | h491
                · linarith only [h0, h410, h411, h491, hc12, hlam, hphi, ht01, u0ehi3]
                · linarith only [h0, h410, h491, hc23, hlam, hphi, ht01, ht12, u0ehi3]
              · linarith only [h411, h488, h490, hlam, hphi, u5ehi7, u5elo3]
            · linarith only [h0, h410, h411, h489, hlam]
          · linarith only [h0, h410, h488, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h497 | h497
        · rcases m.htr 0 2 5 (by decide) (by decide) with h498 | h498
          · rcases m.htr 0 3 4 (by decide) (by decide) with h499 | h499
            · rcases m.htr 0 3 5 (by decide) (by decide) with h500 | h500
              · rcases m.htr 1 2 3 (by decide) (by decide) with h501 | h501
                · rcases m.htr 1 2 5 (by decide) (by decide) with h502 | h502
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h503 | h503
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h504 | h504
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h505 | h505
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h506 | h506
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h507 | h507
                            · linarith only [h497, h505, h507, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · rcases h3bigk with h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h356, hlam, p509_1]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h0, h497, h506, hc12, hlam, hphi, ht01, ht0b, ht5b, p509_1, u5ehi8]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                rcases p509_3 (m.d 0 3) (by simp) with h513 | h513
                                · rcases p509_3 (m.d 1 3) (by simp) with h514 | h514
                                  · rcases p509_3 (m.d 2 3) (by simp) with h515 | h515
                                    · linarith only [h497, h515, hlam]
                                    · linarith only [h505, h515, hlam]
                                  · linarith only [h503, h514, hlam]
                                · linarith only [h513, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                rcases p509_3 (m.d 0 3) (by simp) with h520 | h520
                                · rcases p509_3 (m.d 1 3) (by simp) with h521 | h521
                                  · rcases p509_3 (m.d 2 3) (by simp) with h522 | h522
                                    · linarith only [h497, h522, hlam]
                                    · linarith only [h506, h522, hlam]
                                  · linarith only [h504, h521, hlam]
                                · linarith only [h520, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h501, hc12, hlam, hphi, ht01, p509_1, u0ehi2]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h501, h506, hc12, hlam, hphi, ht01, ht0b, ht5b, p509_1, u5ehi8]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                rcases p509_3 (m.d 0 3) (by simp) with h530 | h530
                                · linarith only [h356, h530, hlam]
                                · linarith only [h499, h530, hlam]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                rcases p509_3 (m.d 0 3) (by simp) with h533 | h533
                                · linarith only [h356, h533, hlam]
                                · linarith only [h500, h533, hlam]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h497, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h501, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                rcases p509_3 (m.d 0 3) (by simp) with h539 | h539
                                · rcases p509_3 (m.d 1 3) (by simp) with h540 | h540
                                  · rcases p509_3 (m.d 2 3) (by simp) with h541 | h541
                                    · rcases p509_3 (m.d 3 4) (by simp) with h542 | h542
                                      · linarith only [h542, hlam, p509_0]
                                      · rcases p509_3 (m.d 3 5) (by simp) with h544 | h544
                                        · linarith only [h506, h544, hlam]
                                        · linarith only [h507, h544, hlam]
                                    · linarith only [h541, hlam, p509_0]
                                  · linarith only [h503, h540, hlam]
                                · linarith only [h499, h539, hlam]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h0, h497, hc12, hlam, hphi, ht01, ht0b, ht5b, p509_1, u5ehi8]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h499, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h503, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h505, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h507, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h500, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h504, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h506, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h506, hc34, hlam, hphi, ht45, p509_1, u5elo2]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [hlam, p509_0]
                          · linarith only [h500, h505, h506, hc34, hlam, hphi, ht45, u5elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h562 | h562
                          · linarith only [h356, h499, h501, h505, h562, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h564 | h564
                            · rcases h3bigk with h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h356, hlam, p565_1]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                rcases p565_3 (m.d 0 3) (by simp) with h568 | h568
                                · rcases p565_3 (m.d 1 3) (by simp) with h569 | h569
                                  · rcases p565_3 (m.d 2 3) (by simp) with h570 | h570
                                    · linarith only [h497, h570, hlam]
                                    · rcases p565_3 (m.d 3 4) (by simp) with h572 | h572
                                      · linarith only [h499, h572, hlam]
                                      · linarith only [h505, h572, hlam]
                                  · linarith only [h501, h569, hlam]
                                · linarith only [h497, h568, hlam]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h356, h501, h564, hc12, hlam, hphi, ht01, ht0b, ht5b, p565_1, u5ehi9]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                rcases p565_3 (m.d 0 3) (by simp) with h578 | h578
                                · rcases p565_3 (m.d 1 3) (by simp) with h579 | h579
                                  · rcases p565_3 (m.d 2 3) (by simp) with h580 | h580
                                    · linarith only [h497, h580, hlam]
                                    · rcases p565_3 (m.d 3 4) (by simp) with h582 | h582
                                      · linarith only [h499, h582, hlam]
                                      · linarith only [h564, h582, hlam]
                                  · linarith only [h504, h579, hlam]
                                · linarith only [h578, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h501, hc12, hlam, hphi, ht01, p565_1, u0ehi2]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                rcases p565_3 (m.d 0 3) (by simp) with h589 | h589
                                · linarith only [h356, h589, hlam]
                                · linarith only [h497, h589, hlam]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h564, hc13, hlam, hphi, ht01, ht0b, ht5b, p565_1, u5ehi9]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                rcases p565_3 (m.d 0 3) (by simp) with h593 | h593
                                · linarith only [h356, h593, hlam]
                                · linarith only [h500, h593, hlam]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h497, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h501, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h505, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h562, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h499, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h503, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                rcases p565_3 (m.d 0 3) (by simp) with h603 | h603
                                · rcases p565_3 (m.d 1 3) (by simp) with h604 | h604
                                  · rcases p565_3 (m.d 2 3) (by simp) with h605 | h605
                                    · linarith only [h605, hlam, p565_0]
                                    · rcases p565_3 (m.d 3 4) (by simp) with h607 | h607
                                      · rcases p565_3 (m.d 3 5) (by simp) with h608 | h608
                                        · linarith only [h564, h608, hlam]
                                        · linarith only [h562, h608, hlam]
                                      · linarith only [h607, hlam, p565_0]
                                  · linarith only [h501, h604, hlam]
                                · linarith only [h497, h603, hlam]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h499, h562, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p565_1]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h500, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h504, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [hc23, hlam, hphi, ht34, ht45, p565_1, u5elo3]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h564, hlam, p565_1]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [hlam, p565_0]
                            · linarith only [h505, h564, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h356, h500, h504, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo0]
                    · linarith only [h356, h503, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h0, h502, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
                · linarith only [h0, h501, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h499, h500, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h627 | h627
              · rcases m.htr 1 2 3 (by decide) (by decide) with h628 | h628
                · rcases m.htr 1 2 5 (by decide) (by decide) with h629 | h629
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h630 | h630
                    · linarith only [h356, h499, h628, h630, hc12, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h356, h630, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h0, h498, h629, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo0]
                · linarith only [h0, h497, h628, hc02, hlam, hphi, u0ehi0]
              · linarith only [h627, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
          · linarith only [h498, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h637 | h637
          · rcases m.htr 0 3 4 (by decide) (by decide) with h638 | h638
            · rcases m.htr 0 3 5 (by decide) (by decide) with h639 | h639
              · rcases m.htr 1 2 3 (by decide) (by decide) with h640 | h640
                · linarith only [h0, h497, h640, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h0, h640, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h497, h637, h639, hlam, hphi, u5ehi7, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h644 | h644
              · rcases m.htr 1 2 3 (by decide) (by decide) with h645 | h645
                · linarith only [h0, h497, h645, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h0, h645, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h497, h637, h644, hlam, hphi, u5ehi7, u5elo3]
          · linarith only [h0, h637, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo2]

theorem n7l_sBT3_M_LI_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0elo := hb0.1
  have h5ehi := hb5.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · linarith only [h3, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
            · linarith only [h0, h3, h6, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h8 | h8
              · rcases m.htr 0 3 5 (by decide) (by decide) with h9 | h9
                · linarith only [h0, h3, h5, h9, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, h3, h5, h8, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h16 | h16
                          · linarith only [h0, h13, h16, h3, h9, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h0, h13, h16, h3, hc23, hc35, hlam, hphi]
                        · linarith only [h15, h8, h9, hc13, hc35, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
                        · linarith only [h13, h14, h20, hlam]
                        · linarith only [h20, h8, h9, hc13, hc35, hlam, hphi]
                    · linarith only [h13, h5, h6, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h24 | h24
                · linarith only [h24, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
                  · linarith only [h2, h26, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
                        · linarith only [h1, h3, h30, h8, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
                          · linarith only [h1, h24, h32, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                          · linarith only [h0, h28, h3, h32, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                        · linarith only [h1, h35, h8, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h37 | h37
                          · linarith only [h1, h37, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                          · linarith only [h2, h28, h29, h3, h37, hc23, hc35, hlam, hphi]
                    · linarith only [h28, h5, h6, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h41 | h41
            · linarith only [h41, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h43 | h43
              · rcases m.htr 0 3 5 (by decide) (by decide) with h44 | h44
                · linarith only [h1, h3, h44, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h46 | h46
                  · linarith only [h43, h44, h46, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
                    · linarith only [h0, h48, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h51 | h51
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h52 | h52
                          · linarith only [h1, h3, h44, h52, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                              · linarith only [h0, h3, h50, h52, h54, h55, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                                · linarith only [h1, h3, h46, h48, h50, h52, h57, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h59 | h59
                                  · linarith only [h1, h3, h41, h48, h50, h54, h57, h59, hlam]
                                  · linarith only [h1, h3, h48, h50, h52, h54, h59, hc34, hc45, hlam, hphi]
                            · linarith only [h0, h43, h5, h50, h54, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h1, h43, h48, h50, h51, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h64 | h64
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h65 | h65
                          · linarith only [h1, h3, h65, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h68 | h68
                              · linarith only [h0, h3, h65, h68, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h70 | h70
                                · linarith only [h67, h68, h70, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
                                  · linarith only [h1, h64, h70, h72, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · linarith only [h1, h3, h64, h65, h72, hc34, hc45, hlam, hphi]
                            · linarith only [h1, h5, h64, h67, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h43, h44, h64, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h77 | h77
                · linarith only [h2, h43, h77, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h79 | h79
                  · linarith only [h2, h3, h79, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h81 | h81
                    · linarith only [h0, h3, h5, h81, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h83 | h83
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
                        · linarith only [h1, h3, h43, h84, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h81, h83, h84, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                        · linarith only [h1, h3, h43, h5, h87, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
                          · linarith only [h1, h77, h89, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                              · linarith only [h2, h3, h81, h87, h89, h92, hc12, hc23, hlam, hphi]
                              · linarith only [h43, h5, h91, h92, hc02, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
                              · linarith only [h91, h95, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h97 | h97
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                                  · rcases h3bigk with h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [hlam, p99_0]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [h1, h3, h79, h81, h97, hc12, hc24, hlam, hphi, p99_1]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [h5, hlam, p99_1]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [h43, hlam, p99_0]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [h77, hlam, p99_0]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [h1, hlam, p99_0]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [hlam, p99_0]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [h81, hlam, p99_1]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [h87, hlam, p99_0]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [h89, hlam, p99_0]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [h95, h98, hc03, hc34, hlam, hphi, p99_1]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [h81, h95, h98, hc12, hc34, hlam, hphi, ht23, p99_1]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [hlam, p99_0]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [h91, hlam, p99_0]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [h95, hlam, p99_0]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      rcases p99_3 (m.d 0 3) (by simp) with h115 | h115
                                      · linarith only [h115, hlam, p99_0]
                                      · rcases p99_3 (m.d 1 3) (by simp) with h117 | h117
                                        · linarith only [h117, h87, hlam]
                                        · rcases p99_3 (m.d 2 3) (by simp) with h119 | h119
                                          · linarith only [h119, h91, hlam]
                                          · linarith only [h119, h5, hlam]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      rcases p99_3 (m.d 0 3) (by simp) with h122 | h122
                                      · linarith only [h122, h43, hlam]
                                      · linarith only [h1, h122, hlam]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [h0, h5, hc12, hc34, hlam, hphi, ht23, p99_1]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [hlam, p99_0]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [h89, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p99_1, u5ehi1]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      rcases p99_3 (m.d 0 3) (by simp) with h128 | h128
                                      · linarith only [h128, hlam, p99_0]
                                      · rcases p99_3 (m.d 1 3) (by simp) with h130 | h130
                                        · linarith only [h130, h89, hlam]
                                        · rcases p99_3 (m.d 2 3) (by simp) with h132 | h132
                                          · linarith only [h132, h95, hlam]
                                          · linarith only [h132, h5, hlam]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      rcases p99_3 (m.d 0 3) (by simp) with h135 | h135
                                      · linarith only [h135, h77, hlam]
                                      · linarith only [h1, h135, hlam]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [h0, h5, hc12, hc35, hlam, hphi, ht23, p99_1]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [h98, hlam, p99_1]
                                    · have p99_0 := h99c.1
                                      have p99_1 := h99c.2.1
                                      have p99_2 := h99c.2.2.1
                                      have p99_3 := h99c.2.2.2
                                      linarith only [hlam, p99_0]
                                  · linarith only [h91, h97, h98, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h142 | h142
                                  · linarith only [h0, h142, h5, h91, h97, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h142, h5, h91, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h145 | h145
        · linarith only [h145, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h147 | h147
          · rcases m.htr 0 2 5 (by decide) (by decide) with h148 | h148
            · linarith only [h148, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h150 | h150
              · linarith only [h1, h150, h2, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h152 | h152
                · linarith only [h0, h147, h152, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h154 | h154
                  · linarith only [h154, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h156 | h156
                    · linarith only [h0, h154, h156, h2, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h147, h154, h156, h2, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h159 | h159
            · linarith only [h159, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h161 | h161
              · linarith only [h1, h161, h2, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h163 | h163
                · linarith only [h161, h163, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h165 | h165
                  · linarith only [h165, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h167 | h167
                    · linarith only [h0, h165, h167, h2, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h169 | h169
                      · linarith only [h1, h165, h167, h169, h2, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                        · linarith only [h1, h165, h171, h2, hc34, hc45, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
                          · linarith only [h1, h147, h163, h165, h173, h2, hc02, hc45, hlam, hphi, ht23, ht34]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                            · linarith only [h0, h171, h175, h2, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h177 | h177
                              · linarith only [h145, h173, h175, h177, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h179 | h179
                                · linarith only [h1, h165, h167, h179, h2, hc12, hc24, hlam, hphi]
                                · linarith only [h1, h167, h169, h179, h2, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h182 | h182
      · rcases m.htr 0 1 5 (by decide) (by decide) with h183 | h183
        · linarith only [h183, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h185 | h185
          · linarith only [h0, h1, h185, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h187 | h187
            · linarith only [h185, h187, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h189 | h189
              · rcases m.htr 0 3 5 (by decide) (by decide) with h190 | h190
                · linarith only [h190, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h192 | h192
                  · linarith only [h1, h182, h190, h192, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h194 | h194
                    · linarith only [h0, h1, h190, h194, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h196 | h196
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h197 | h197
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h198 | h198
                          · linarith only [h0, h1, h190, h194, h196, h198, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h1, h196, h198, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h196, h197, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h202 | h202
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h203 | h203
                          · linarith only [h1, h182, h190, h194, h196, h203, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h182, h196, h203, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h182, h196, h202, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h182, h189, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h208 | h208
        · linarith only [h208, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h210 | h210
          · linarith only [h0, h1, h210, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h212 | h212
            · linarith only [h0, h1, h212, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h214 | h214
              · rcases m.htr 0 3 5 (by decide) (by decide) with h215 | h215
                · linarith only [h215, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h217 | h217
                  · linarith only [h214, h215, h217, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h219 | h219
                    · linarith only [h0, h182, h210, h214, h215, h219, hc02, hc35, hlam, hphi, ht23]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h221 | h221
                      · linarith only [h0, h182, h217, h221, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h223 | h223
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h224 | h224
                          · linarith only [h0, h182, h214, h215, h219, h224, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h224, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h214, h223, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h228 | h228
                · linarith only [h214, h228, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h230 | h230
                  · linarith only [h230, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h232 | h232
                    · linarith only [h0, h1, h214, h230, h232, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h234 | h234
                      · linarith only [h0, h1, h214, h230, h234, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h236 | h236
                        · linarith only [h0, h1, h214, h232, h236, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h236, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h239 | h239
    · rcases m.htr 0 1 4 (by decide) (by decide) with h240 | h240
      · rcases m.htr 0 1 5 (by decide) (by decide) with h241 | h241
        · linarith only [h241, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h243 | h243
          · rcases m.htr 0 2 5 (by decide) (by decide) with h244 | h244
            · linarith only [h244, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h246 | h246
              · rcases m.htr 0 3 5 (by decide) (by decide) with h247 | h247
                · linarith only [h0, h239, h244, h247, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h249 | h249
                  · linarith only [h0, h239, h244, h246, h249, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h251 | h251
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h252 | h252
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h253 | h253
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h254 | h254
                          · linarith only [h0, h239, h244, h247, h254, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h256 | h256
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h257 | h257
                              · linarith only [h239, h241, h251, h254, h257, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h259 | h259
                                · linarith only [h0, h239, h244, h249, h252, h253, h259, hlam]
                                · linarith only [h0, h239, h244, h251, h256, h259, hc34, hc45, hlam, hphi]
                            · linarith only [h239, h241, h253, h254, h256, hc23, hc35, hlam, hphi]
                        · linarith only [h246, h247, h253, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h240, h252, hlam]
                    · linarith only [h0, h243, h251, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h266 | h266
                · linarith only [h240, h246, h266, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h268 | h268
                  · linarith only [h0, h240, h244, h268, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h270 | h270
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h271 | h271
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h272 | h272
                        · linarith only [h0, h239, h246, h272, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h274 | h274
                          · linarith only [h239, h266, h274, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h276 | h276
                            · linarith only [h243, h246, h276, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h278 | h278
                              · linarith only [h239, h240, h241, h270, h274, h278, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h280 | h280
                                · linarith only [h268, h271, h280, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h282 | h282
                                  · linarith only [h0, h240, h244, h270, h272, h280, h282, hc23, hc34, hlam, hphi]
                                  · rcases h3bigk with h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h246, h270, h282, hc23, hc45, hlam, hphi, ht34, p284_1]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h246, h282, hc23, hc45, hlam, hphi, ht34, p284_1]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h246, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h266, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h239, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h240, h272, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p284_1, u0elo0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h272, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h274, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h243, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h270, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h276, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h278, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h282, hc03, hc45, hlam, hphi, ht34, p284_1]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h270, h282, hc23, hc45, hlam, hphi, ht34, p284_1]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h282, hc23, hc45, hlam, hphi, ht34, p284_1]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h282, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      rcases p284_3 (m.d 0 3) (by simp) with h305 | h305
                                      · linarith only [h305, hlam, p284_0]
                                      · rcases p284_3 (m.d 1 3) (by simp) with h307 | h307
                                        · linarith only [h274, h307, hlam]
                                        · rcases p284_3 (m.d 2 3) (by simp) with h309 | h309
                                          · linarith only [h278, h309, hlam]
                                          · rcases p284_3 (m.d 3 4) (by simp) with h311 | h311
                                            · linarith only [h282, h311, hlam]
                                            · linarith only [h246, h311, hlam]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      rcases p284_3 (m.d 0 3) (by simp) with h314 | h314
                                      · linarith only [h266, h314, hlam]
                                      · linarith only [h239, h314, hlam]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      rcases p284_3 (m.d 0 3) (by simp) with h317 | h317
                                      · linarith only [h266, h317, hlam]
                                      · linarith only [h243, h317, hlam]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h239, h246, h270, h282, hc23, hc45, hlam, hphi, ht34, p284_1]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [hlam, p284_0]
                      · linarith only [h0, h240, h271, hlam]
                    · linarith only [h0, h243, h270, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h0, h239, h243, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h325 | h325
        · linarith only [h0, h325, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h327 | h327
          · rcases m.htr 0 2 5 (by decide) (by decide) with h328 | h328
            · linarith only [h328, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h330 | h330
              · linarith only [h239, h240, h330, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h332 | h332
                · linarith only [h0, h239, h328, h332, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h334 | h334
                  · linarith only [h334, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h336 | h336
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h337 | h337
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h338 | h338
                        · linarith only [h239, h240, h330, h334, h338, hc03, hc45, hlam, hphi, ht34]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h340 | h340
                          · linarith only [h239, h332, h340, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h342 | h342
                            · linarith only [h240, h327, h338, h342, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h344 | h344
                              · linarith only [h239, h325, h336, h340, h344, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h346 | h346
                                · linarith only [h239, h240, h334, h336, h337, h338, h346, hc23, hc34, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h348 | h348
                                  · linarith only [h239, h240, h334, h336, h348, hc23, hc34, hlam, hphi]
                                  · linarith only [h239, h240, h336, h338, h348, hc23, hc45, hlam, hphi, ht34]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h351 | h351
                        · linarith only [h239, h330, h351, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h353 | h353
                          · linarith only [h239, h332, h353, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h355 | h355
                            · linarith only [h0, h327, h337, h351, h355, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h0, h239, h336, h337, h355, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h327, h336, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h0, h239, h327, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h360 | h360
      · rcases m.htr 0 1 5 (by decide) (by decide) with h361 | h361
        · linarith only [h361, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h363 | h363
          · rcases m.htr 0 2 5 (by decide) (by decide) with h364 | h364
            · linarith only [h364, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h366 | h366
              · rcases m.htr 0 3 5 (by decide) (by decide) with h367 | h367
                · linarith only [h363, h364, h367, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h369 | h369
                  · linarith only [h239, h360, h363, h364, h369, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h371 | h371
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h372 | h372
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h373 | h373
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h375 | h375
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h376 | h376
                              · linarith only [h239, h363, h367, h376, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                              · linarith only [h363, h364, h371, h374, h375, h376, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h366, h367, h371, h374, h375, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h380 | h380
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h381 | h381
                              · linarith only [h239, h360, h372, h374, h380, h381, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h383 | h383
                                · linarith only [h360, h369, h372, h383, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                                · linarith only [h363, h364, h380, h383, hc34, hc45, hlam, hphi]
                            · linarith only [h239, h366, h374, h380, hc23, hc35, hlam, hphi]
                        · linarith only [h239, h360, h366, h373, hlam]
                      · linarith only [h0, h360, h372, hlam]
                    · linarith only [h0, h363, h371, hlam]
              · linarith only [h239, h360, h366, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h391 | h391
            · linarith only [h363, h391, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h393 | h393
              · rcases m.htr 0 3 5 (by decide) (by decide) with h394 | h394
                · linarith only [h394, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h396 | h396
                  · linarith only [h0, h360, h363, h394, h396, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h398 | h398
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h399 | h399
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h400 | h400
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h401 | h401
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h402 | h402
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h403 | h403
                              · linarith only [h0, h363, h394, h398, h403, hc01, hc12, hlam, hphi]
                              · linarith only [h0, h360, h363, h399, h401, h402, h403, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h360, h363, h393, h399, h402, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h407 | h407
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h408 | h408
                              · linarith only [h239, h360, h399, h401, h407, h408, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h410 | h410
                                · linarith only [h360, h396, h399, h410, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h412 | h412
                                  · linarith only [h0, h360, h363, h398, h399, h401, h407, h410, h412, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                                  · linarith only [h0, h360, h363, h398, h399, h401, h407, h412, hc34, hc45, hlam, hphi]
                            · linarith only [h0, h360, h363, h393, h399, h407, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h0, h360, h363, h393, h398, h399, h400, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h0, h360, h363, h398, h399, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h418 | h418
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h419 | h419
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h420 | h420
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h421 | h421
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h422 | h422
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h423 | h423
                                · linarith only [h360, h418, h423, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h425 | h425
                                  · linarith only [h0, h360, h363, h394, h418, h421, h422, h423, h425, hlam]
                                  · rcases h3bigk with h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h239, hlam, p427_1]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h363, hlam, p427_1]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h394, h398, h420, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p427_1]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h394, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      rcases p427_3 (m.d 0 3) (by simp) with h433 | h433
                                      · linarith only [h239, h433, hlam]
                                      · rcases p427_3 (m.d 1 3) (by simp) with h435 | h435
                                        · rcases p427_3 (m.d 2 3) (by simp) with h436 | h436
                                          · rcases p427_3 (m.d 3 4) (by simp) with h437 | h437
                                            · linarith only [h419, h437, hlam]
                                            · rcases p427_3 (m.d 3 5) (by simp) with h439 | h439
                                              · linarith only [h420, h439, hlam]
                                              · linarith only [h394, h439, hlam]
                                          · linarith only [h363, h436, hlam]
                                        · linarith only [h239, h435, hlam]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h398, hlam, p427_1]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h393, h394, h420, hlam, p427_2]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h0, h363, h394, h398, hc01, hc23, hlam, hphi, ht12, p427_1]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      rcases p427_3 (m.d 0 3) (by simp) with h448 | h448
                                      · linarith only [h363, h448, hlam]
                                      · rcases p427_3 (m.d 1 3) (by simp) with h450 | h450
                                        · linarith only [h398, h450, hlam]
                                        · linarith only [h239, h450, hlam]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h239, h360, h418, h421, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p427_1]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h0, h360, h398, h418, h421, hlam, p427_2]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h0, h360, h363, h394, h418, h421, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p427_1]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h393, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h419, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h421, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h425, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h0, h360, h363, h418, h420, h421, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p427_1]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h420, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h422, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      rcases p427_3 (m.d 0 3) (by simp) with h465 | h465
                                      · linarith only [h394, h465, hlam]
                                      · linarith only [h393, h465, hlam]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [hlam, p427_0]
                              · linarith only [h398, h420, h422, hlam]
                            · linarith only [h398, h420, h421, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h471 | h471
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h472 | h472
                              · linarith only [h0, h360, h398, h418, h420, h471, h472, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h360, h398, h418, h471, h472, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h360, h398, h418, h471, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h360, h393, h398, h419, hlam]
                      · linarith only [h0, h360, h418, hlam]
              · linarith only [h0, h360, h363, h393, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h479 | h479
        · linarith only [h479, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h481 | h481
          · rcases m.htr 0 2 5 (by decide) (by decide) with h482 | h482
            · linarith only [h482, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h484 | h484
              · rcases m.htr 0 3 5 (by decide) (by decide) with h485 | h485
                · linarith only [h481, h482, h485, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h487 | h487
                  · linarith only [h481, h482, h484, h487, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h489 | h489
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h490 | h490
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h491 | h491
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h492 | h492
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h493 | h493
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h494 | h494
                              · linarith only [h360, h481, h484, h485, h494, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                              · linarith only [h481, h482, h489, h492, h493, h494, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h484, h485, h489, h492, h493, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h498 | h498
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h499 | h499
                              · linarith only [h481, h492, h499, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h501 | h501
                                · linarith only [h487, h490, h501, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                · linarith only [h481, h482, h498, h501, hc34, hc45, hlam, hphi]
                            · linarith only [h484, h485, h498, hc23, hc35, hlam, hphi]
                        · linarith only [h239, h484, h491, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h506 | h506
                        · linarith only [h489, h490, h506, hlam]
                        · linarith only [h484, h485, h506, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h481, h489, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h510 | h510
                · linarith only [h484, h510, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h512 | h512
                  · linarith only [h512, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h514 | h514
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h515 | h515
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h516 | h516
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h517 | h517
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h518 | h518
                            · linarith only [h481, h482, h484, h510, h514, h517, h518, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h520 | h520
                              · linarith only [h481, h510, h520, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h522 | h522
                                · linarith only [h512, h515, h522, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h524 | h524
                                  · linarith only [h481, h482, h514, h516, h522, h524, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                  · rcases h3bigk with h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h239, hlam, p526_1]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h484, hc23, hc34, hlam, hphi, p526_1]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h484, hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h510, hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      rcases p526_3 (m.d 0 3) (by simp) with h532 | h532
                                      · linarith only [h239, h532, hlam]
                                      · rcases p526_3 (m.d 1 3) (by simp) with h534 | h534
                                        · rcases p526_3 (m.d 2 3) (by simp) with h535 | h535
                                          · linarith only [h514, h535, hlam]
                                          · rcases p526_3 (m.d 3 4) (by simp) with h537 | h537
                                            · linarith only [h516, h537, hlam]
                                            · linarith only [h484, h537, hlam]
                                        · linarith only [h239, h534, hlam]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h481, h482, h517, h520, hlam, p526_2]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h239, h484, h514, hc01, hc12, hlam, hphi, p526_1]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h482, h514, h520, hc12, hlam, hphi, ht01, ht0b, ht5b, p526_1, u5ehi0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h481, hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h514, hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h518, hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h520, hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h239, h514, h516, hc01, hc12, hlam, hphi, p526_1]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h516, hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h524, hc23, hc45, hlam, hphi, ht34, p526_1]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h524, hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h239, h514, h517, hc01, hc12, hlam, hphi, p526_1]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h517, hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      rcases p526_3 (m.d 0 3) (by simp) with h557 | h557
                                      · linarith only [h510, h557, hlam]
                                      · linarith only [h481, h557, hlam]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h239, h484, h514, h517, hc01, hc12, hlam, hphi, p526_1]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [hlam, p526_0]
                          · linarith only [h239, h484, h516, h517, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h563 | h563
                          · linarith only [h516, h563, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h565 | h565
                            · linarith only [h481, h516, h565, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h567 | h567
                              · linarith only [h239, h481, h563, h567, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h569 | h569
                                · linarith only [h512, h515, h569, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h571 | h571
                                  · linarith only [h481, h482, h569, h571, hc23, hc34, hlam, hphi]
                                  · linarith only [h239, h516, h571, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h574 | h574
                        · linarith only [h239, h484, h514, h515, h574, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h576 | h576
                          · linarith only [h510, h574, h576, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h578 | h578
                            · linarith only [h481, h574, h578, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h580 | h580
                              · linarith only [h239, h481, h576, h580, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h582 | h582
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h583 | h583
                                  · rcases h3bigk with h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h239, hlam, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h484, h512, h578, h582, hc23, hc34, hlam, hphi, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h484, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h510, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h514, h515, h578, hc03, hc34, hlam, hphi, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h514, h515, h578, hc23, hc34, hlam, hphi, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h574, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h576, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h481, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h514, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h578, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h580, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      rcases p584_3 (m.d 0 3) (by simp) with h600 | h600
                                      · linarith only [h600, hlam, p584_0]
                                      · rcases p584_3 (m.d 1 3) (by simp) with h602 | h602
                                        · linarith only [h574, h602, hlam]
                                        · linarith only [h239, h602, hlam]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h239, hc01, hc34, hlam, hphi, ht12, ht23, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      rcases p584_3 (m.d 0 3) (by simp) with h606 | h606
                                      · linarith only [h484, h606, hlam]
                                      · linarith only [h481, h606, hlam]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p584_1, u5ehi3]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      rcases p584_3 (m.d 0 3) (by simp) with h611 | h611
                                      · linarith only [h611, hlam, p584_0]
                                      · rcases p584_3 (m.d 1 3) (by simp) with h613 | h613
                                        · linarith only [h576, h613, hlam]
                                        · linarith only [h239, h613, hlam]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h239, hc01, hc35, hlam, hphi, ht12, ht23, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      rcases p584_3 (m.d 0 3) (by simp) with h617 | h617
                                      · linarith only [h510, h617, hlam]
                                      · linarith only [h481, h617, hlam]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h583, hlam, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [hlam, p584_0]
                                  · linarith only [h578, h582, h583, hlam]
                                · linarith only [h0, h515, h582, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h481, h514, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h625 | h625
            · linarith only [h625, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h627 | h627
              · rcases m.htr 0 3 5 (by decide) (by decide) with h628 | h628
                · linarith only [h628, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h630 | h630
                  · linarith only [h630, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h632 | h632
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h633 | h633
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h634 | h634
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h635 | h635
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h636 | h636
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h637 | h637
                              · linarith only [h628, h632, h637, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                              · linarith only [h0, h481, h632, h635, h637, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h481, h627, h628, h632, h635, h636, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h641 | h641
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h642 | h642
                              · linarith only [h632, h635, h642, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h644 | h644
                                · linarith only [h630, h633, h644, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h646 | h646
                                  · linarith only [h481, h627, h642, h644, h646, hlam]
                                  · rcases h3bigk with h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [hlam, p648_0]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h239, hlam, p648_1]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h481, hlam, p648_1]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h239, h635, h646, hc34, hc45, hlam, hphi, p648_1]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h628, hlam, p648_0]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h635, h646, hc03, hc45, hlam, hphi, ht34, p648_1]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [hlam, p648_0]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h0, h481, h635, h646, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p648_1]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h635, h646, hc34, hc45, hlam, hphi, p648_1]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h635, hlam, p648_0]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h627, h632, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p648_1]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h632, hlam, p648_0]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [hlam, p648_0]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h632, h635, h646, hc34, hc45, hlam, hphi, p648_1]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h642, hlam, p648_0]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h627, hlam, p648_0]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h634, hlam, p648_0]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h641, hlam, p648_0]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [hlam, p648_0]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h646, hlam, p648_0]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h627, h646, hc34, hc45, hlam, hphi, p648_1]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h0, h481, h632, h646, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p648_1]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [h0, h481, h646, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p648_1]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      rcases p648_3 (m.d 0 3) (by simp) with h672 | h672
                                      · linarith only [h628, h672, hlam]
                                      · linarith only [h627, h672, hlam]
                                    · have p648_0 := h648c.1
                                      have p648_1 := h648c.2.1
                                      have p648_2 := h648c.2.2.1
                                      have p648_3 := h648c.2.2.2
                                      linarith only [hlam, p648_0]
                            · linarith only [h0, h481, h627, h641, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h481, h627, h632, h634, hlam]
                      · linarith only [h0, h481, h632, h633, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h679 | h679
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h680 | h680
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h681 | h681
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h682 | h682
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h683 | h683
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h684 | h684
                                · linarith only [h679, h684, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h686 | h686
                                  · linarith only [h627, h628, h683, h684, h686, hlam]
                                  · rcases h3bigk with h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [hlam, p688_0]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [h239, hlam, p688_1]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [h481, hlam, p688_1]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [h628, h632, h681, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p688_1]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [h628, hlam, p688_0]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      rcases p688_3 (m.d 0 3) (by simp) with h694 | h694
                                      · linarith only [h239, h694, hlam]
                                      · rcases p688_3 (m.d 1 3) (by simp) with h696 | h696
                                        · rcases p688_3 (m.d 2 3) (by simp) with h697 | h697
                                          · rcases p688_3 (m.d 3 4) (by simp) with h698 | h698
                                            · linarith only [h680, h698, hlam]
                                            · rcases p688_3 (m.d 3 5) (by simp) with h700 | h700
                                              · linarith only [h681, h700, hlam]
                                              · linarith only [h628, h700, hlam]
                                          · linarith only [h481, h697, hlam]
                                        · linarith only [h239, h696, hlam]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [hlam, p688_0]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [h632, hlam, p688_1]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [h627, h628, h681, hlam, p688_2]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [h632, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p688_1, u5ehi3]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      rcases p688_3 (m.d 0 3) (by simp) with h709 | h709
                                      · linarith only [h481, h709, hlam]
                                      · rcases p688_3 (m.d 1 3) (by simp) with h711 | h711
                                        · linarith only [h632, h711, hlam]
                                        · linarith only [h239, h711, hlam]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [h681, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p688_1, u5ehi1]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [hlam, p688_0]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [h627, h628, h632, h681, hlam, p688_2]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [h627, h628, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p688_1]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [h627, hlam, p688_0]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [h680, hlam, p688_0]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [h682, hlam, p688_0]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [hlam, p688_0]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [h686, hlam, p688_0]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [h627, h681, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p688_1]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [h681, hlam, p688_0]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [h683, hlam, p688_0]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      rcases p688_3 (m.d 0 3) (by simp) with h726 | h726
                                      · linarith only [h628, h726, hlam]
                                      · linarith only [h627, h726, hlam]
                                    · have p688_0 := h688c.1
                                      have p688_1 := h688c.2.1
                                      have p688_2 := h688c.2.2.1
                                      have p688_3 := h688c.2.2.2
                                      linarith only [hlam, p688_0]
                              · linarith only [h632, h681, h683, hlam]
                            · linarith only [h627, h632, h682, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h732 | h732
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h733 | h733
                              · linarith only [h239, h681, h733, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h360, h632, h679, h733, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h360, h632, h679, h732, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h239, h627, h680, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h738 | h738
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h739 | h739
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h740 | h740
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h741 | h741
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h742 | h742
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h743 | h743
                                  · linarith only [h627, h628, h630, h632, h739, h743, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                                  · rcases h3bigk with h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c | h745c
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [hlam, p745_0]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [h239, hlam, p745_1]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [h481, hlam, p745_1]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [h628, h740, h742, h743, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p745_1]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [h628, hlam, p745_0]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      rcases p745_3 (m.d 0 3) (by simp) with h751 | h751
                                      · linarith only [h239, h751, hlam]
                                      · rcases p745_3 (m.d 1 3) (by simp) with h753 | h753
                                        · rcases p745_3 (m.d 2 3) (by simp) with h754 | h754
                                          · rcases p745_3 (m.d 3 4) (by simp) with h755 | h755
                                            · linarith only [h738, h755, hlam]
                                            · rcases p745_3 (m.d 3 5) (by simp) with h757 | h757
                                              · linarith only [h739, h757, hlam]
                                              · linarith only [h628, h757, hlam]
                                          · linarith only [h481, h754, hlam]
                                        · linarith only [h239, h753, hlam]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [hlam, p745_0]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [h632, hlam, p745_1]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [h627, h628, h739, hlam, p745_2]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [h627, h628, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p745_1]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      rcases p745_3 (m.d 0 3) (by simp) with h766 | h766
                                      · linarith only [h481, h766, hlam]
                                      · rcases p745_3 (m.d 1 3) (by simp) with h768 | h768
                                        · linarith only [h632, h768, hlam]
                                        · linarith only [h239, h768, hlam]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [h239, hc01, hc23, hlam, hphi, ht12, p745_1]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [hlam, p745_0]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [h627, h628, h632, h739, hlam, p745_2]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [h627, h628, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p745_1]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [h627, hlam, p745_0]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [h738, hlam, p745_0]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [h740, hlam, p745_0]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [hlam, p745_0]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [h743, hlam, p745_0]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [h627, h632, h739, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p745_1]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [h739, hlam, p745_0]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [h741, hlam, p745_0]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      rcases p745_3 (m.d 0 3) (by simp) with h783 | h783
                                      · linarith only [h628, h783, hlam]
                                      · linarith only [h627, h783, hlam]
                                    · have p745_0 := h745c.1
                                      have p745_1 := h745c.2.1
                                      have p745_2 := h745c.2.2.1
                                      have p745_3 := h745c.2.2.2
                                      linarith only [hlam, p745_0]
                                · linarith only [h0, h679, h742, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                              · linarith only [h632, h739, h741, hlam]
                            · linarith only [h627, h628, h632, h739, h740, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h790 | h790
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h791 | h791
                              · linarith only [h239, h739, h791, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h632, h791, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h627, h632, h790, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h239, h627, h738, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h796 | h796
                · linarith only [h796, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h798 | h798
                  · linarith only [h798, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h800 | h800
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h801 | h801
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h802 | h802
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h803 | h803
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h804 | h804
                            · linarith only [h239, h627, h800, h804, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h481, h802, h804, hc01, hc13, hlam, hphi]
                          · linarith only [h0, h481, h627, h802, h803, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h808 | h808
                          · linarith only [h802, h808, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h810 | h810
                            · linarith only [h239, h802, h810, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h812 | h812
                              · linarith only [h800, h808, h812, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h814 | h814
                                · linarith only [h801, h814, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h816 | h816
                                  · linarith only [h0, h481, h810, h814, h816, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · linarith only [h0, h481, h800, h802, h816, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h481, h800, h801, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h820 | h820
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h821 | h821
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h822 | h822
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h823 | h823
                            · linarith only [h0, h481, h627, h800, h820, h823, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h800, h823, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h481, h627, h821, h822, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h800, h820, h821, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h828 | h828
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h829 | h829
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h830 | h830
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h831 | h831
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h832 | h832
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h833 | h833
                                  · linarith only [h0, h481, h627, h798, h828, h833, hc01, hc13, hlam, hphi]
                                  · linarith only [h0, h481, h627, h832, h833, hc01, hc24, hlam, hphi, ht12]
                                · linarith only [h0, h820, h832, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                              · linarith only [h0, h800, h831, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h796, h800, h828, h829, h830, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                          · linarith only [h0, h481, h627, h828, h829, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h840 | h840
                          · linarith only [h828, h840, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h842 | h842
                            · linarith only [h239, h828, h842, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h800, h842, hc01, hc34, hlam, hphi, ht12, ht23]

theorem n7l_sBT3_M_LR_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h2, h7, h9, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                    · linarith only [h0, h11, h2, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · linarith only [h0, h11, h2, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
                · linarith only [h0, h14, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
                  · linarith only [h0, h14, h16, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
                    · linarith only [h0, h14, h18, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · linarith only [h0, h18, h2, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
              · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
                · linarith only [h0, h22, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                  · linarith only [h0, h2, h22, h24, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
                    · linarith only [h26, h5, hc13, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h28 | h28
                      · linarith only [h1, h28, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · linarith only [h21, h26, h28, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                · linarith only [h0, h31, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
                  · linarith only [h0, h2, h31, h33, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                    · linarith only [h35, h5, hc13, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h37 | h37
                      · linarith only [h21, h37, hc14, hlam, hphi, ht01, u0ehi8]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                        · linarith only [h0, h2, h39, h5, hlam, hphi, u0ehi7, u0elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h41 | h41
                          · linarith only [h0, h21, h3, h41, h5, hlam, hphi, u0ehi7, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                            · linarith only [h21, h43, h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                            · linarith only [h0, h31, h39, h4, h41, h43, h5, hc12, hc45, hlam, hphi, ht23, ht34, u0ehi7, u0elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h46 | h46
            · rcases m.htr 0 4 5 (by decide) (by decide) with h47 | h47
              · linarith only [h3, h4, h47, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
                · linarith only [h0, h49, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · linarith only [h2, h4, h49, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h52 | h52
              · linarith only [h3, h4, h52, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                · linarith only [h0, h54, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · linarith only [h2, h4, h54, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h57 | h57
          · rcases m.htr 0 3 4 (by decide) (by decide) with h58 | h58
            · linarith only [h2, h3, h58, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h60 | h60
              · rcases m.htr 1 2 3 (by decide) (by decide) with h61 | h61
                · linarith only [h0, h61, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · linarith only [h2, h3, h61, hc12, hc24, hlam, hphi]
              · linarith only [h2, h3, h60, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h65 | h65
            · linarith only [h2, h3, h65, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h67 | h67
              · rcases m.htr 1 2 3 (by decide) (by decide) with h68 | h68
                · linarith only [h0, h68, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · linarith only [h2, h57, h68, hc12, hc25, hlam, hphi]
              · linarith only [h2, h3, h67, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h72 | h72
        · rcases m.htr 0 2 5 (by decide) (by decide) with h73 | h73
          · rcases m.htr 0 3 4 (by decide) (by decide) with h74 | h74
            · rcases m.htr 0 4 5 (by decide) (by decide) with h75 | h75
              · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
                · linarith only [h2, h72, h75, h76, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h80 | h80
                      · linarith only [h1, h80, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · linarith only [h2, h72, h75, h79, h80, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h74, h79, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h2, h72, h78, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
                · linarith only [h2, h73, h85, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h87 | h87
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                      · linarith only [h0, h87, h89, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                        · linarith only [h0, h87, h91, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h2, h88, h91, hc13, hlam, hphi, ht01, u0ehi6]
                    · linarith only [h74, h88, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h2, h72, h87, hc12, hc23, hlam, hphi]
            · linarith only [h2, h72, h74, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h97 | h97
            · rcases m.htr 0 4 5 (by decide) (by decide) with h98 | h98
              · linarith only [h72, h73, h98, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h100 | h100
                · linarith only [h0, h100, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h102 | h102
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h103 | h103
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
                      · linarith only [h104, h98, hc14, hlam, hphi, ht01, u0ehi8]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                        · linarith only [h0, h102, h106, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h106, h2, h97, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h103, h97, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h102, h2, h72, hc12, hc23, hlam, hphi]
            · linarith only [h2, h72, h97, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h112 | h112
          · rcases m.htr 0 3 4 (by decide) (by decide) with h113 | h113
            · rcases m.htr 0 4 5 (by decide) (by decide) with h114 | h114
              · rcases m.htr 1 2 3 (by decide) (by decide) with h115 | h115
                · linarith only [h0, h115, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
                  · linarith only [h0, h117, h72, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h120 | h120
                      · linarith only [h1, h120, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · linarith only [h113, h114, h119, h120, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                    · linarith only [h113, h119, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
              · linarith only [h112, h114, h72, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h125 | h125
              · rcases m.htr 1 2 3 (by decide) (by decide) with h126 | h126
                · linarith only [h112, h126, h2, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h128 | h128
                  · linarith only [h0, h112, h128, h72, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h130 | h130
                    · linarith only [h112, h113, h130, h2, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h132 | h132
                      · linarith only [h1, h132, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · linarith only [h125, h130, h132, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
              · linarith only [h112, h113, h125, h2, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h136 | h136
            · rcases m.htr 0 4 5 (by decide) (by decide) with h137 | h137
              · rcases m.htr 1 2 3 (by decide) (by decide) with h138 | h138
                · linarith only [h0, h138, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h140 | h140
                  · linarith only [h0, h140, h72, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h142 | h142
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h143 | h143
                      · linarith only [h1, h143, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · linarith only [h136, h137, h142, h143, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                    · linarith only [h136, h142, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h147 | h147
                · linarith only [h147, h2, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h149 | h149
                  · linarith only [h0, h149, h72, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h151 | h151
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h152 | h152
                      · linarith only [h1, h137, h152, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h154 | h154
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h155 | h155
                          · linarith only [h137, h154, h155, h72, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                          · linarith only [h155, h72, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                        · linarith only [h1, h151, h154, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · linarith only [h136, h151, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h160 | h160
              · rcases m.htr 1 2 3 (by decide) (by decide) with h161 | h161
                · linarith only [h161, h2, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h163 | h163
                  · linarith only [h0, h163, h72, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h165 | h165
                    · linarith only [h136, h165, h2, hc13, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h167 | h167
                      · linarith only [h1, h167, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · linarith only [h160, h165, h167, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
                · linarith only [h170, h2, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h172 | h172
                  · linarith only [h0, h172, h72, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h174 | h174
                    · linarith only [h136, h174, h2, hc13, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h176 | h176
                      · linarith only [h1, h136, h160, h176, h2, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h178 | h178
                        · linarith only [h136, h178, h2, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                        · linarith only [h178, h2, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h181 | h181
      · rcases m.htr 0 2 4 (by decide) (by decide) with h182 | h182
        · linarith only [h0, h1, h182, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h184 | h184
          · rcases m.htr 0 3 4 (by decide) (by decide) with h185 | h185
            · linarith only [h0, h1, h181, h185, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h187 | h187
              · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
                · linarith only [h0, h188, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · linarith only [h181, h182, h188, hc12, hc24, hlam, hphi]
              · linarith only [h0, h1, h181, h187, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h192 | h192
            · linarith only [h0, h1, h181, h192, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h194 | h194
              · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
                · linarith only [h0, h1, h195, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                · linarith only [h181, h182, h195, hc12, hc24, hlam, hphi]
              · linarith only [h0, h1, h181, h194, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h199 | h199
        · linarith only [h0, h1, h199, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h201 | h201
          · rcases m.htr 0 3 4 (by decide) (by decide) with h202 | h202
            · rcases m.htr 0 4 5 (by decide) (by decide) with h203 | h203
              · rcases m.htr 1 2 3 (by decide) (by decide) with h204 | h204
                · linarith only [h181, h201, h204, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h206 | h206
                  · linarith only [h0, h199, h201, h206, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h208 | h208
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h209 | h209
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h210 | h210
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h211 | h211
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h212 | h212
                            · linarith only [h202, h212, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                            · linarith only [h201, h211, h212, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                          · linarith only [h199, h202, h203, h211, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1, h201, h204, h208, h210, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h0, h1, h201, h202, h203, h209, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
                    · linarith only [h202, h208, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
              · linarith only [h0, h1, h201, h203, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h220 | h220
              · rcases m.htr 1 2 3 (by decide) (by decide) with h221 | h221
                · linarith only [h0, h181, h201, h221, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h223 | h223
                  · linarith only [h0, h1, h199, h201, h223, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h225 | h225
                    · linarith only [h202, h225, hc13, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h227 | h227
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h228 | h228
                        · linarith only [h0, h1, h225, h228, hc12, hc23, hlam, hphi]
                        · linarith only [h181, h201, h228, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h0, h1, h201, h220, h227, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
              · linarith only [h0, h1, h201, h220, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h233 | h233
            · rcases m.htr 0 4 5 (by decide) (by decide) with h234 | h234
              · rcases m.htr 1 2 3 (by decide) (by decide) with h235 | h235
                · linarith only [h181, h235, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h237 | h237
                  · linarith only [h0, h199, h237, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h239 | h239
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h240 | h240
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h241 | h241
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h242 | h242
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h243 | h243
                            · linarith only [h233, h243, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                            · linarith only [h233, h234, h243, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                          · linarith only [h199, h233, h234, h242, hlam, hphi, u0ehi6, u0elo2]
                        · linarith only [h0, h1, h235, h239, h241, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1, h233, h234, h240, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h233, h239, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h250 | h250
                · linarith only [h0, h1, h234, h250, hc45, hlam, hphi, ht34, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h252 | h252
                  · linarith only [h0, h1, h234, h252, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h254 | h254
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h255 | h255
                      · linarith only [h0, h1, h234, h254, h255, hc13, hlam, hphi, ht01, u0ehi6]
                      · linarith only [h0, h1, h255, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                    · linarith only [h233, h254, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h259 | h259
              · rcases m.htr 1 2 3 (by decide) (by decide) with h260 | h260
                · linarith only [h0, h260, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h262 | h262
                  · linarith only [h0, h1, h199, h262, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
                    · linarith only [h181, h233, h264, hc13, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h266 | h266
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h267 | h267
                        · linarith only [h0, h1, h264, h267, hc12, hc23, hlam, hphi]
                        · linarith only [h181, h267, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                      · linarith only [h0, h1, h259, h266, hlam, hphi, u0ehi6, u0elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h271 | h271
                · linarith only [h181, h271, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h273 | h273
                  · linarith only [h0, h1, h259, h273, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h275 | h275
                    · linarith only [h181, h233, h275, hc13, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h277 | h277
                      · linarith only [h0, h1, h259, h277, hc14, hlam, hphi, ht01, u0ehi6]
                      · linarith only [h0, h1, h277, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h280 | h280
    · rcases m.htr 0 2 3 (by decide) (by decide) with h281 | h281
      · rcases m.htr 0 2 4 (by decide) (by decide) with h282 | h282
        · rcases m.htr 0 2 5 (by decide) (by decide) with h283 | h283
          · rcases m.htr 0 3 4 (by decide) (by decide) with h284 | h284
            · rcases m.htr 0 4 5 (by decide) (by decide) with h285 | h285
              · rcases m.htr 1 2 3 (by decide) (by decide) with h286 | h286
                · rcases m.htr 1 2 4 (by decide) (by decide) with h287 | h287
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h288 | h288
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h289 | h289
                      · linarith only [h280, h289, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · linarith only [h0, h280, h285, h288, h289, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h284, h288, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h0, h280, h285, h287, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · linarith only [h0, h280, h285, h286, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h295 | h295
                · rcases m.htr 1 2 4 (by decide) (by decide) with h296 | h296
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h297 | h297
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h298 | h298
                      · linarith only [h280, h285, h298, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h300 | h300
                        · linarith only [h281, h300, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h284, h300, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                    · linarith only [h281, h284, h297, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                  · linarith only [h0, h296, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h280, h295, hc23, hlam, hphi, ht01, ht12, u0ehi8]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h306 | h306
              · rcases m.htr 1 2 3 (by decide) (by decide) with h307 | h307
                · rcases m.htr 1 2 4 (by decide) (by decide) with h308 | h308
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h309 | h309
                    · linarith only [h284, h309, hc13, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h311 | h311
                      · linarith only [h280, h311, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · linarith only [h0, h280, h306, h307, h309, h311, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h280, h306, h308, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · linarith only [h0, h280, h306, h307, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h316 | h316
                · rcases m.htr 1 2 4 (by decide) (by decide) with h317 | h317
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h318 | h318
                    · linarith only [h284, h318, hc13, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h320 | h320
                      · linarith only [h280, h284, h306, h320, hlam, hphi, u0ehi7, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h322 | h322
                        · linarith only [h284, h316, h322, hc13, hlam, hphi, ht01, u0ehi7]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h324 | h324
                          · linarith only [h0, h280, h284, h306, h317, h324, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h326 | h326
                            · linarith only [h284, h306, h326, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                            · linarith only [h0, h280, h284, h316, h318, h326, hc12, hc45, hlam, hphi, ht01, ht34, u0ehi7, u3ehi2]
                  · linarith only [h0, h317, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h280, h284, h316, hc23, hlam, hphi, ht01, ht12, u0ehi7]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h331 | h331
            · rcases m.htr 0 4 5 (by decide) (by decide) with h332 | h332
              · linarith only [h0, h280, h283, h332, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h334 | h334
                · rcases m.htr 1 2 4 (by decide) (by decide) with h335 | h335
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h336 | h336
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h337 | h337
                      · linarith only [h0, h280, h283, h332, h337, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h339 | h339
                        · linarith only [h281, h283, h339, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h331, h339, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                    · linarith only [h281, h283, h331, h336, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h0, h335, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h280, h334, hc23, hlam, hphi, ht01, ht12, u0ehi8]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h345 | h345
              · linarith only [h0, h280, h283, h345, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h347 | h347
                · rcases m.htr 1 2 4 (by decide) (by decide) with h348 | h348
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h349 | h349
                    · linarith only [h331, h349, hc13, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h351 | h351
                      · linarith only [h0, h280, h283, h345, h351, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h353 | h353
                        · linarith only [h331, h347, h353, hc13, hlam, hphi, ht01, u0ehi7]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h355 | h355
                          · linarith only [h0, h280, h283, h331, h345, h348, h355, hc25, hlam, hphi, ht01, ht12, u0ehi7]
                          · linarith only [h0, h280, h283, h349, h355, hc45, hlam, hphi, ht34, u3ehi1]
                  · linarith only [h0, h348, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h280, h281, h331, h347, hlam, hphi, u0ehi7, u0elo1]
        · linarith only [h0, h280, h282, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h361 | h361
        · rcases m.htr 0 2 5 (by decide) (by decide) with h362 | h362
          · rcases m.htr 0 3 4 (by decide) (by decide) with h363 | h363
            · rcases m.htr 0 4 5 (by decide) (by decide) with h364 | h364
              · rcases m.htr 1 2 3 (by decide) (by decide) with h365 | h365
                · linarith only [h281, h362, h365, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h280, h364, h365, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h368 | h368
                · linarith only [h0, h280, h281, h368, hc12, hlam, hphi, ht01, u0ehi8]
                · linarith only [h0, h280, h368, hc23, hlam, hphi, ht01, ht12, u0ehi8]
            · linarith only [h0, h280, h281, h363, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h372 | h372
            · rcases m.htr 0 4 5 (by decide) (by decide) with h373 | h373
              · linarith only [h0, h280, h362, h373, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h375 | h375
                · linarith only [h0, h281, h375, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h280, h375, hc23, hlam, hphi, ht01, ht12, u0ehi8]
            · linarith only [h0, h280, h281, h372, hlam]
        · linarith only [h0, h280, h361, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h380 | h380
      · rcases m.htr 0 2 4 (by decide) (by decide) with h381 | h381
        · rcases m.htr 0 2 5 (by decide) (by decide) with h382 | h382
          · rcases m.htr 0 3 4 (by decide) (by decide) with h383 | h383
            · rcases m.htr 0 4 5 (by decide) (by decide) with h384 | h384
              · rcases m.htr 1 2 3 (by decide) (by decide) with h385 | h385
                · rcases m.htr 1 2 4 (by decide) (by decide) with h386 | h386
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h387 | h387
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h388 | h388
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h389 | h389
                        · linarith only [h380, h389, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h383, h389, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                      · linarith only [h280, h384, h388, hlam, hphi, u0ehi5, u0elo3]
                    · linarith only [h380, h383, h387, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                  · linarith only [h0, h381, h386, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h0, h385, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h396 | h396
                · rcases m.htr 1 2 4 (by decide) (by decide) with h397 | h397
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h398 | h398
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h399 | h399
                      · linarith only [h384, h396, h398, h399, hc12, hlam, hphi, ht01, u0ehi8]
                      · linarith only [h280, h399, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                    · linarith only [h380, h383, h398, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                  · linarith only [h0, h381, h397, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h0, h380, h396, hlam, hphi, u0ehi5, u0elo1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h405 | h405
              · rcases m.htr 1 2 3 (by decide) (by decide) with h406 | h406
                · rcases m.htr 1 2 4 (by decide) (by decide) with h407 | h407
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h408 | h408
                    · linarith only [h383, h408, hc13, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h410 | h410
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h411 | h411
                        · linarith only [h280, h380, h408, h411, hlam, hphi, u0ehi5, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h413 | h413
                          · linarith only [h381, h413, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                          · linarith only [h405, h411, h413, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                      · linarith only [h280, h381, h405, h410, hlam, hphi, u0ehi5, u0elo1]
                  · linarith only [h0, h407, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h406, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h419 | h419
                · rcases m.htr 1 2 4 (by decide) (by decide) with h420 | h420
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h421 | h421
                    · linarith only [h383, h421, hc13, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h423 | h423
                      · linarith only [h405, h420, h423, hc12, hlam, hphi, ht01, u0ehi8]
                      · linarith only [h280, h423, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                  · linarith only [h0, h381, h420, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h0, h380, h419, hlam, hphi, u0ehi5, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h428 | h428
            · rcases m.htr 0 4 5 (by decide) (by decide) with h429 | h429
              · linarith only [h381, h382, h429, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h431 | h431
                · rcases m.htr 1 2 4 (by decide) (by decide) with h432 | h432
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h433 | h433
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h434 | h434
                      · linarith only [h429, h431, h433, h434, hc12, hlam, hphi, ht01, u0ehi8]
                      · linarith only [h280, h380, h382, h428, h434, hc25, hc45, hlam, hphi, ht01, ht12, ht34, u0ehi5, u3ehi3]
                    · linarith only [h380, h382, h428, h433, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h381, h382, h432, hc12, hc25, hlam, hphi]
                · linarith only [h0, h380, h382, h431, hc25, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h440 | h440
              · linarith only [h381, h382, h440, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h442 | h442
                · rcases m.htr 1 2 4 (by decide) (by decide) with h443 | h443
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h444 | h444
                    · linarith only [h428, h444, hc13, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h446 | h446
                      · linarith only [h440, h443, h446, hc12, hlam, hphi, ht01, u0ehi8]
                      · linarith only [h280, h446, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                  · linarith only [h381, h382, h443, hc12, hc25, hlam, hphi]
                · linarith only [h0, h380, h382, h442, hc25, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h451 | h451
          · rcases m.htr 0 3 4 (by decide) (by decide) with h452 | h452
            · linarith only [h380, h381, h452, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h454 | h454
              · rcases m.htr 1 2 3 (by decide) (by decide) with h455 | h455
                · rcases m.htr 1 2 4 (by decide) (by decide) with h456 | h456
                  · linarith only [h380, h381, h456, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h456, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h380, h455, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h380, h381, h454, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h461 | h461
            · linarith only [h380, h381, h461, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h463 | h463
              · rcases m.htr 1 2 3 (by decide) (by decide) with h464 | h464
                · rcases m.htr 1 2 4 (by decide) (by decide) with h465 | h465
                  · linarith only [h381, h465, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h465, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h380, h464, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h380, h381, h463, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h470 | h470
        · rcases m.htr 0 2 5 (by decide) (by decide) with h471 | h471
          · rcases m.htr 0 3 4 (by decide) (by decide) with h472 | h472
            · rcases m.htr 0 4 5 (by decide) (by decide) with h473 | h473
              · rcases m.htr 1 2 3 (by decide) (by decide) with h474 | h474
                · linarith only [h380, h471, h474, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h474, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h477 | h477
                · linarith only [h380, h477, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h477, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h380, h470, h472, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h481 | h481
            · rcases m.htr 0 4 5 (by decide) (by decide) with h482 | h482
              · linarith only [h470, h471, h482, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h484 | h484
                · linarith only [h380, h484, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h484, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h380, h470, h481, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h488 | h488
          · rcases m.htr 0 3 4 (by decide) (by decide) with h489 | h489
            · rcases m.htr 0 4 5 (by decide) (by decide) with h490 | h490
              · rcases m.htr 1 2 3 (by decide) (by decide) with h491 | h491
                · linarith only [h380, h488, h491, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h491, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h470, h488, h490, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h495 | h495
              · rcases m.htr 1 2 3 (by decide) (by decide) with h496 | h496
                · linarith only [h0, h380, h496, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h496, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h380, h488, h489, h495, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h500 | h500
            · rcases m.htr 0 4 5 (by decide) (by decide) with h501 | h501
              · rcases m.htr 1 2 3 (by decide) (by decide) with h502 | h502
                · linarith only [h0, h380, h502, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h502, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h505 | h505
                · linarith only [h0, h380, h505, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h505, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h508 | h508
              · rcases m.htr 1 2 3 (by decide) (by decide) with h509 | h509
                · linarith only [h0, h380, h509, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h509, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h512 | h512
                · linarith only [h0, h380, h512, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h512, hc23, hlam, hphi, ht01, ht12, u0ehi5]

end R2N4
