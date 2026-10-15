import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3176000 in
set_option maxHeartbeats 3176000 in
theorem r1l7_20_12_13_15_H_I_L_0_L_0_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2elo := hb2.1
  have h3elo := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                                · linarith only [h0, h14, h16, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                · rcases h0bigk with h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [hlam, p18_0]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h0, h16, h6, h8, h9, hc01, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1, u3elo0]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h16, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h16, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h16, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h0, hlam, p18_0]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [hlam, p18_0]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h16, h6, h8, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h16, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p18_1, u2elo0]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p18_1, u2elo0]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h1, hlam, p18_1]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h3, hlam, p18_1]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [hlam, p18_0]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h16, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p18_1, u3elo0]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p18_1, u3elo0]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p18_1]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h4, hlam, p18_0]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h6, hlam, p18_0]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [hlam, p18_0]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h16, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p18_1, u3elo0]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h2, hlam, p18_0]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h5, hlam, p18_1]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h7, hlam, p18_0]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [h8, hlam, p18_1]
                                  · have p18_0 := h18c.1
                                    have p18_1 := h18c.2.1
                                    have p18_2 := h18c.2.2.1
                                    have p18_3 := h18c.2.2.2
                                    linarith only [hlam, p18_0]
                              · linarith only [h14, h15, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                            · linarith only [h14, h6, hc23, hlam, hphi, u3elo0]
                          · linarith only [h13, h7, hc13, hlam, hphi, u3elo0]
                        · linarith only [h12, h6, h9, hc23, hlam, hphi, u3elo0]
                      · linarith only [h11, h5, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h10, h4, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h3, h9, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h51 | h51
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h54 | h54
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h55 | h55
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h57 | h57
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
                                · linarith only [h51, h56, h58, h8, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases h0bigk with h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [hlam, p60_0]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [h0, h51, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p60_1]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [h3, h57, hc01, hc35, hlam, hphi, ht0b, ht5b, p60_1]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    rcases p60_3 (m.d 0 1) (by simp) with h64 | h64
                                    · rcases p60_3 (m.d 0 2) (by simp) with h65 | h65
                                      · linarith only [h0, h65, hlam]
                                      · linarith only [h4, h65, hlam]
                                    · linarith only [h64, hlam, p60_0]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    rcases p60_3 (m.d 0 1) (by simp) with h69 | h69
                                    · rcases p60_3 (m.d 0 2) (by simp) with h70 | h70
                                      · linarith only [h0, h70, hlam]
                                      · linarith only [h5, h70, hlam]
                                    · linarith only [h2, h69, hlam]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [h0, hlam, p60_0]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [hlam, p60_0]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p60_1, u2elo0]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [h4, h56, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p60_1, u2elo0]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p60_1, u2elo0]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [h1, hlam, p60_1]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [h3, hlam, p60_1]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [hlam, p60_0]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [h4, h56, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p60_1, u3elo0]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [h2, h53, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p60_1, u3elo0]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [h8, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p60_1]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [h4, hlam, p60_0]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [h6, hlam, p60_0]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [hlam, p60_0]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [h8, hlam, p60_0]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [h2, hlam, p60_0]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [h5, hlam, p60_1]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [h7, hlam, p60_0]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [h4, h5, h56, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p60_1, u2elo0]
                                  · have p60_0 := h60c.1
                                    have p60_1 := h60c.2.1
                                    have p60_2 := h60c.2.2.1
                                    have p60_3 := h60c.2.2.2
                                    linarith only [hlam, p60_0]
                              · linarith only [h57, h7, hc23, hlam, hphi, u3elo0]
                            · linarith only [h56, h6, hc23, hlam, hphi, u3elo0]
                          · linarith only [h55, h7, hc13, hlam, hphi, u3elo0]
                        · linarith only [h51, h54, h6, hc23, hlam, hphi, u3elo0]
                      · linarith only [h5, h51, h53, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h4, h51, h52, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h3, h51, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h101 | h101
                · linarith only [h101, h6, h7, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h106 | h106
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h107 | h107
                          · linarith only [h1, h107, h7, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                              · linarith only [h1, h103, h110, h7, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h112 | h112
                                · linarith only [h1, h101, h103, h109, h112, h7, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · rcases h0bigk with h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h0, h105, h110, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p114_1]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p114_1]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    rcases p114_3 (m.d 0 1) (by simp) with h118 | h118
                                    · rcases p114_3 (m.d 0 2) (by simp) with h119 | h119
                                      · linarith only [h0, h119, hlam]
                                      · linarith only [h119, h4, hlam]
                                    · linarith only [h118, hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h1, h103, h109, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p114_1]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h0, hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h1, h103, h109, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p114_1]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h109, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p114_1, u2elo0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h1, h103, h109, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p114_1, u2elo0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h1, hlam, p114_1]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h3, hlam, p114_1]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h109, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p114_1, u3elo4]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h7, hlam, p114_1]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h0, h105, h109, h110, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p114_1]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h4, hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h6, hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h101, hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h2, hlam, p114_0]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h5, hlam, p114_1]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h1, h103, h109, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p114_1]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [h7, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p114_1, u3elo4]
                                  · have p114_0 := h114c.1
                                    have p114_1 := h114c.2.1
                                    have p114_2 := h114c.2.2.1
                                    have p114_3 := h114c.2.2.2
                                    linarith only [hlam, p114_0]
                            · linarith only [h109, h6, hc23, hlam, hphi, u3elo0]
                        · linarith only [h106, h6, h7, hc13, hlam, hphi, u3elo4]
                      · linarith only [h103, h105, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h103, h104, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h103, h3, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h149 | h149
              · rcases m.htr 0 4 5 (by decide) (by decide) with h150 | h150
                · rcases m.htr 1 2 3 (by decide) (by decide) with h151 | h151
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h152 | h152
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h153 | h153
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h154 | h154
                        · linarith only [h154, h6, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h156 | h156
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h157 | h157
                            · linarith only [h1, h151, h156, h157, h6, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h159 | h159
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h160 | h160
                                · rcases h0bigk with h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [hlam, p161_0]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h159, h160, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p161_1]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h1, h151, h159, h160, hc01, hc45, hlam, hphi, ht0b, ht5b, p161_1]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h1, h151, h159, h160, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p161_1]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    rcases p161_3 (m.d 0 1) (by simp) with h166 | h166
                                    · rcases p161_3 (m.d 0 2) (by simp) with h167 | h167
                                      · linarith only [h0, h167, hlam]
                                      · linarith only [h167, h5, hlam]
                                    · linarith only [h166, h2, hlam]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h0, hlam, p161_0]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [hlam, p161_0]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h1, h151, h159, h160, hc02, hc45, hlam, hphi, ht0b, ht5b, p161_1]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h1, h151, h159, h160, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p161_1, u2elo0]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p161_1, u2elo0]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h1, hlam, p161_1]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h3, hlam, p161_1]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [hlam, p161_0]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h6, hlam, p161_1]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h153, h2, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p161_1, u3elo3]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h0, h152, h157, h159, h160, hc04, hc45, hlam, hphi, ht0b, ht5b, p161_1]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h4, hlam, p161_0]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h6, hc03, hlam, hphi, p161_1, u3elo3]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [hlam, p161_0]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h153, h159, h160, h2, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p161_1, u3elo3]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h2, hlam, p161_0]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h5, hlam, p161_1]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h149, hlam, p161_0]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [h150, hlam, p161_1]
                                  · have p161_0 := h161c.1
                                    have p161_1 := h161c.2.1
                                    have p161_2 := h161c.2.2.1
                                    have p161_3 := h161c.2.2.2
                                    linarith only [hlam, p161_0]
                                · linarith only [h150, h160, h6, hlam]
                              · linarith only [h149, h159, h6, hc23, hlam, hphi, u3elo3]
                          · linarith only [h149, h156, h6, hc13, hlam, hphi, u3elo3]
                      · linarith only [h151, h153, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h151, h152, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h151, h3, hc12, hlam, hphi, u2elo0]
                · linarith only [h149, h150, h6, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h198 | h198
                · rcases m.htr 1 2 3 (by decide) (by decide) with h199 | h199
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h200 | h200
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h201 | h201
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h202 | h202
                        · linarith only [h1, h202, h6, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h204 | h204
                          · linarith only [h1, h149, h204, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h206 | h206
                            · linarith only [h199, h206, h6, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h208 | h208
                              · linarith only [h1, h149, h199, h208, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h210 | h210
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
                                    linarith only [h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p211_1]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    rcases p211_3 (m.d 0 1) (by simp) with h214 | h214
                                    · rcases p211_3 (m.d 0 2) (by simp) with h215 | h215
                                      · linarith only [h0, h215, hlam]
                                      · linarith only [h215, h3, hlam]
                                    · linarith only [h1, h214, hlam]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [h198, hc01, hc45, hlam, hphi, ht0b, ht5b, p211_1]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    rcases p211_3 (m.d 0 1) (by simp) with h220 | h220
                                    · rcases p211_3 (m.d 0 2) (by simp) with h221 | h221
                                      · linarith only [h0, h221, hlam]
                                      · linarith only [h221, h5, hlam]
                                    · linarith only [h2, h220, hlam]
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
                                    linarith only [h1, h199, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p211_1, u2elo0]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [h198, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p211_1, u2elo0]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [h1, h149, h199, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p211_1, u2elo0]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [h1, hlam, p211_1]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [h3, hlam, p211_1]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [hlam, p211_0]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [h6, hlam, p211_1]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [h149, hlam, p211_1]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [h0, h200, h206, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p211_1]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [h4, hlam, p211_0]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [h1, h199, h6, hc23, hlam, hphi, p211_1, u3elo3]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [hlam, p211_0]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [h1, h149, h199, h6, hc23, hlam, hphi, p211_1, u3elo3]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [h2, hlam, p211_0]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [h5, hlam, p211_1]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [h1, h199, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p211_1, u2elo0]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [h198, hlam, p211_1]
                                  · have p211_0 := h211c.1
                                    have p211_1 := h211c.2.1
                                    have p211_2 := h211c.2.2.1
                                    have p211_3 := h211c.2.2.2
                                    linarith only [hlam, p211_0]
                                · linarith only [h198, h210, h6, hlam]
                      · linarith only [h201, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h199, h200, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h199, h3, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h249 | h249
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h250 | h250
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h251 | h251
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h252 | h252
                        · linarith only [h1, h252, h6, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h254 | h254
                          · linarith only [h1, h149, h254, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h256 | h256
                            · linarith only [h1, h249, h256, h6, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h258 | h258
                              · linarith only [h1, h149, h249, h258, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h260 | h260
                                · linarith only [h198, h256, h260, h4, hc23, hlam, hphi, u3elo3]
                                · rcases h0bigk with h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [hlam, p262_0]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [h0, h250, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p262_1]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    rcases p262_3 (m.d 0 1) (by simp) with h265 | h265
                                    · rcases p262_3 (m.d 0 2) (by simp) with h266 | h266
                                      · linarith only [h0, h266, hlam]
                                      · linarith only [h266, h3, hlam]
                                    · linarith only [h1, h265, hlam]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    rcases p262_3 (m.d 0 1) (by simp) with h270 | h270
                                    · rcases p262_3 (m.d 0 2) (by simp) with h271 | h271
                                      · linarith only [h0, h271, hlam]
                                      · linarith only [h271, h4, hlam]
                                    · linarith only [h270, hlam, p262_0]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    rcases p262_3 (m.d 0 1) (by simp) with h275 | h275
                                    · rcases p262_3 (m.d 0 2) (by simp) with h276 | h276
                                      · linarith only [h0, h276, hlam]
                                      · linarith only [h276, h5, hlam]
                                    · linarith only [h2, h275, hlam]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [h0, hlam, p262_0]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [hlam, p262_0]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p262_1, u2elo0]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [h1, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p262_1, u2elo0]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [h1, h198, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p262_1, u2elo0]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [h1, hlam, p262_1]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [h3, hlam, p262_1]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [hlam, p262_0]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [h6, hlam, p262_1]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [h149, hlam, p262_1]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p262_1]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [h4, hlam, p262_0]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [h260, h6, hc03, hlam, hphi, p262_1, u3elo4]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [hlam, p262_0]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [h198, hlam, p262_0]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [h2, hlam, p262_0]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [h5, hlam, p262_1]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [h1, h149, hc13, hlam, hphi, p262_1, u3elo4]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [h149, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p262_1, u3elo4]
                                  · have p262_0 := h262c.1
                                    have p262_1 := h262c.2.1
                                    have p262_2 := h262c.2.2.1
                                    have p262_3 := h262c.2.2.2
                                    linarith only [hlam, p262_0]
                      · linarith only [h251, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h249, h250, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h249, h3, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h303 | h303
            · rcases m.htr 0 3 5 (by decide) (by decide) with h304 | h304
              · linarith only [h3, h304, h5, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h306 | h306
                · linarith only [h306, h4, h5, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h308 | h308
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h309 | h309
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h310 | h310
                      · linarith only [h0, h310, h5, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h312 | h312
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h313 | h313
                          · linarith only [h1, h304, h313, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h315 | h315
                            · linarith only [h0, h308, h315, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                            · linarith only [h1, h304, h312, h315, hc23, hlam, hphi, u3elo4]
                        · linarith only [h303, h304, h312, hc13, hlam, hphi, u3elo4]
                    · linarith only [h309, h4, h5, hc12, hlam, hphi, u2elo4]
                  · linarith only [h3, h308, h5, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h321 | h321
              · linarith only [h3, h303, h321, h5, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h323 | h323
                · linarith only [h323, h4, h5, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h325 | h325
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h326 | h326
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h327 | h327
                      · linarith only [h0, h327, h5, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h329 | h329
                        · linarith only [h303, h329, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h331 | h331
                          · linarith only [h1, h303, h321, h331, h5, hc02, hlam, hphi, ht23, u3elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h333 | h333
                            · linarith only [h0, h325, h333, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h335 | h335
                              · linarith only [h0, h321, h326, h333, h335, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                              · linarith only [h3, h335, h5, hc23, hlam, hphi, u3elo4]
                    · linarith only [h325, h326, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h3, h325, h5, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h340 | h340
          · rcases m.htr 0 3 4 (by decide) (by decide) with h341 | h341
            · linarith only [h3, h341, h4, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h343 | h343
              · rcases m.htr 0 4 5 (by decide) (by decide) with h344 | h344
                · rcases m.htr 1 2 3 (by decide) (by decide) with h345 | h345
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h346 | h346
                    · linarith only [h0, h346, h4, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h348 | h348
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h349 | h349
                        · linarith only [h1, h341, h349, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h351 | h351
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h352 | h352
                            · linarith only [h0, h1, h341, h345, h352, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                            · linarith only [h0, h345, h352, h4, hc23, hlam, hphi, u3elo3]
                          · linarith only [h341, h343, h351, hc13, hlam, hphi, u3elo3]
                      · linarith only [h340, h345, h348, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h3, h345, h4, hc12, hlam, hphi, u2elo3]
                · linarith only [h3, h341, h343, h344, h4, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h359 | h359
                · rcases m.htr 1 2 3 (by decide) (by decide) with h360 | h360
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h361 | h361
                    · linarith only [h0, h361, h4, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h363 | h363
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h364 | h364
                        · linarith only [h1, h341, h364, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h366 | h366
                          · linarith only [h1, h343, h366, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h368 | h368
                            · linarith only [h0, h341, h360, h368, h4, hlam]
                            · linarith only [h0, h360, h368, h4, hc23, hlam, hphi, u3elo3]
                      · linarith only [h340, h360, h363, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h3, h360, h4, hc12, hlam, hphi, u2elo3]
                · linarith only [h340, h359, h4, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h374 | h374
            · linarith only [h3, h374, h4, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h376 | h376
              · linarith only [h3, h340, h376, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h378 | h378
                · rcases m.htr 1 2 3 (by decide) (by decide) with h379 | h379
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h380 | h380
                    · linarith only [h0, h380, h4, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h382 | h382
                      · linarith only [h0, h340, h382, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h384 | h384
                        · linarith only [h1, h374, h384, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h386 | h386
                          · linarith only [h1, h376, h386, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h388 | h388
                            · linarith only [h0, h374, h379, h388, h4, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                            · linarith only [h3, h388, h4, hc23, hlam, hphi, u3elo3]
                  · linarith only [h3, h379, h4, hc12, hlam, hphi, u2elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h392 | h392
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h393 | h393
                    · linarith only [h0, h393, h4, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h395 | h395
                      · linarith only [h0, h340, h395, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h397 | h397
                        · linarith only [h1, h374, h397, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h399 | h399
                          · linarith only [h1, h376, h399, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h401 | h401
                            · linarith only [h0, h374, h392, h4, h401, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                            · linarith only [h3, h4, h401, hc23, hlam, hphi, u3elo3]
                  · linarith only [h3, h392, h4, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h405 | h405
        · rcases m.htr 0 2 5 (by decide) (by decide) with h406 | h406
          · rcases m.htr 0 3 4 (by decide) (by decide) with h407 | h407
            · rcases m.htr 0 3 5 (by decide) (by decide) with h408 | h408
              · rcases m.htr 0 4 5 (by decide) (by decide) with h409 | h409
                · rcases m.htr 1 2 3 (by decide) (by decide) with h410 | h410
                  · linarith only [h3, h410, hc02, hlam, hphi, u2elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h412 | h412
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h413 | h413
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h414 | h414
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h415 | h415
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h416 | h416
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h417 | h417
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h418 | h418
                                · linarith only [h0, h3, h412, h416, h418, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                                · linarith only [h3, h405, h409, h418, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                              · linarith only [h3, h417, hc02, hlam, hphi, ht23, u3elo4]
                            · linarith only [h3, h416, hc02, hlam, hphi, ht23, u3elo3]
                          · linarith only [h408, h415, hc13, hlam, hphi, u3elo0]
                        · linarith only [h3, h407, h410, h412, h414, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · linarith only [h406, h412, h413, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · linarith only [h3, h405, h412, hc12, hlam, hphi, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h427 | h427
                  · linarith only [h3, h427, hc02, hlam, hphi, u2elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h429 | h429
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h430 | h430
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h431 | h431
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h432 | h432
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h433 | h433
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h434 | h434
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h435 | h435
                                · linarith only [h0, h3, h409, h429, h433, h435, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                · rcases h0bigk with h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h0, h430, hc01, hc25, hlam, hphi, ht0b, ht5b, p437_1]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h1, h427, h430, h434, hc01, hc35, hlam, hphi, ht0b, ht5b, p437_1]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    rcases p437_3 (m.d 0 1) (by simp) with h441 | h441
                                    · rcases p437_3 (m.d 0 2) (by simp) with h442 | h442
                                      · linarith only [h0, h442, hlam]
                                      · linarith only [h405, h442, hlam]
                                    · linarith only [h441, hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    rcases p437_3 (m.d 0 1) (by simp) with h446 | h446
                                    · rcases p437_3 (m.d 0 2) (by simp) with h447 | h447
                                      · linarith only [h0, h447, hlam]
                                      · linarith only [h406, h447, hlam]
                                    · linarith only [h2, h446, hlam]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h0, hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h3, hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h3, h405, h433, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p437_1, u3elo2]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p437_1, u2elo0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h1, hlam, p437_1]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [hc02, hlam, hphi, ht23, p437_1, u3elo0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h3, h405, h433, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p437_1, u3elo2]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h3, h406, h434, h435, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p437_1, u3elo2]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h409, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p437_1]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h405, hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h407, hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h409, hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h2, hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h406, hlam, p437_1]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h408, hlam, p437_0]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [h3, h405, h406, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p437_1, u3elo2]
                                  · have p437_0 := h437c.1
                                    have p437_1 := h437c.2.1
                                    have p437_2 := h437c.2.2.1
                                    have p437_3 := h437c.2.2.2
                                    linarith only [hlam, p437_0]
                              · linarith only [h3, h434, hc02, hlam, hphi, ht23, u3elo4]
                            · linarith only [h3, h433, hc02, hlam, hphi, ht23, u3elo3]
                          · linarith only [h408, h432, hc13, hlam, hphi, u3elo0]
                        · linarith only [h3, h405, h407, h427, h431, hc12, hlam, hphi, ht23, u3elo2]
                      · linarith only [h3, h406, h429, h430, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · linarith only [h3, h405, h429, hc12, hlam, hphi, ht23, u3elo2]
              · linarith only [h3, h406, h408, hlam]
            · linarith only [h3, h405, h407, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h479 | h479
            · rcases m.htr 0 3 5 (by decide) (by decide) with h480 | h480
              · rcases m.htr 0 4 5 (by decide) (by decide) with h481 | h481
                · linarith only [h405, h406, h481, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h483 | h483
                  · linarith only [h0, h3, h405, h483, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h485 | h485
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h486 | h486
                      · linarith only [h0, h406, h486, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h488 | h488
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h489 | h489
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h490 | h490
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h491 | h491
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h492 | h492
                                · linarith only [h0, h406, h481, h485, h490, h491, h492, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                · rcases h0bigk with h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h0, h485, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p494_1]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h1, h485, h486, h489, h490, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p494_1]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    rcases p494_3 (m.d 0 1) (by simp) with h498 | h498
                                    · rcases p494_3 (m.d 0 2) (by simp) with h499 | h499
                                      · linarith only [h0, h499, hlam]
                                      · linarith only [h405, h499, hlam]
                                    · linarith only [h498, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h2, h485, h486, h490, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p494_1]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h0, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h3, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h405, h406, h490, h491, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p494_1, u3elo2]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h406, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h1, hlam, p494_1]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hc02, hlam, hphi, ht23, p494_1, u3elo0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h3, h405, h490, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p494_1, u3elo2]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h2, h3, h485, h486, h490, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p494_1, u3elo2]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h0, h485, h490, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p494_1]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h405, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h479, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h481, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h2, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h0, h485, h490, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p494_1]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h480, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h406, h491, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p494_1, u3elo2]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hlam, p494_0]
                              · linarith only [h3, h489, h491, hc03, hlam, hphi, u3elo1]
                            · linarith only [h3, h490, hc02, hlam, hphi, ht23, u3elo3]
                          · linarith only [h480, h489, hc13, hlam, hphi, u3elo0]
                        · linarith only [h405, h406, h479, h483, h488, hc12, hlam, hphi, u2elo4]
                    · linarith only [h3, h405, h485, hc12, hlam, hphi, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h529 | h529
                · linarith only [h405, h406, h529, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h531 | h531
                  · linarith only [h0, h3, h531, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h533 | h533
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h534 | h534
                      · linarith only [h0, h406, h534, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h536 | h536
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h537 | h537
                          · linarith only [h0, h1, h3, h480, h533, h537, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h539 | h539
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h540 | h540
                              · linarith only [h0, h3, h480, h533, h539, h540, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                              · linarith only [h0, h3, h533, h539, h540, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                            · linarith only [h0, h3, h533, h539, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h479, h480, h536, hc13, hlam, hphi, u3elo4]
                    · linarith only [h3, h405, h480, h533, hc12, hlam, hphi, ht23, u3elo4]
            · linarith only [h3, h405, h479, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h547 | h547
          · rcases m.htr 0 3 4 (by decide) (by decide) with h548 | h548
            · rcases m.htr 0 3 5 (by decide) (by decide) with h549 | h549
              · rcases m.htr 0 4 5 (by decide) (by decide) with h550 | h550
                · rcases m.htr 1 2 3 (by decide) (by decide) with h551 | h551
                  · linarith only [h0, h3, h551, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h553 | h553
                    · linarith only [h0, h405, h553, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h555 | h555
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h556 | h556
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h557 | h557
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h558 | h558
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h559 | h559
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h560 | h560
                                · rcases h0bigk with h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h547, h559, h560, hc01, hc45, hlam, hphi, ht0b, ht5b, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h1, h556, h560, hc01, hc45, hlam, hphi, ht0b, ht5b, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h0, h405, h555, h559, h560, hc01, hc45, hlam, hphi, ht0b, ht5b, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    rcases p561_3 (m.d 0 1) (by simp) with h566 | h566
                                    · rcases p561_3 (m.d 0 2) (by simp) with h567 | h567
                                      · linarith only [h0, h567, hlam]
                                      · linarith only [h547, h567, hlam]
                                    · linarith only [h2, h566, hlam]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h0, hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h3, hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h405, hlam, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h405, h558, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p561_1, u3elo2]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h1, hlam, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h0, h555, hc03, hc25, hlam, hphi, ht0b, ht5b, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h0, h3, h405, h555, h559, h560, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p561_1, u3elo2]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h3, h547, h559, h560, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p561_1, u3elo2]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h0, h555, h559, h560, hc04, hc45, hlam, hphi, ht0b, ht5b, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h0, h555, h559, h560, hc04, hc45, hlam, hphi, ht0b, ht5b, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h548, hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h2, h3, h548, h555, h559, h560, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p561_1, u3elo2]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h2, hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h547, hlam, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h549, hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h550, hlam, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [hlam, p561_0]
                                · rcases h0bigk with h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [hlam, p591_0]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h0, h555, h559, h560, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p591_1]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h0, h3, h555, h559, h560, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p591_1]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h550, h560, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p591_1]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h550, h560, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p591_1]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h0, hlam, p591_0]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [hlam, p591_0]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h3, hlam, p591_0]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h405, hlam, p591_1]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h550, h560, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p591_1]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h1, hlam, p591_1]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [hc02, hlam, hphi, ht23, p591_1, u3elo0]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [hlam, p591_0]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h550, hc03, hc45, hlam, hphi, ht0b, ht5b, p591_1]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h2, h3, h555, h559, h560, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p591_1, u3elo2]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p591_1]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h405, h558, hc02, hlam, hphi, ht23, p591_1, u3elo2]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h548, hlam, p591_0]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [hlam, p591_0]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h405, h550, h558, h560, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p591_1, u3elo2]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h2, hlam, p591_0]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h547, hlam, p591_1]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h549, hlam, p591_0]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [h550, hlam, p591_1]
                                  · have p591_0 := h591c.1
                                    have p591_1 := h591c.2.1
                                    have p591_2 := h591c.2.2.1
                                    have p591_3 := h591c.2.2.2
                                    linarith only [hlam, p591_0]
                              · linarith only [h405, h558, h559, hc02, hlam, hphi, ht23, u3elo4]
                            · linarith only [h0, h3, h555, h558, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                          · linarith only [h549, h556, h557, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · linarith only [h3, h548, h551, h555, h556, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                      · linarith only [h3, h547, h555, hc12, hlam, hphi, ht23, u3elo2]
                · linarith only [h405, h547, h550, hlam]
              · linarith only [h3, h547, h549, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h624 | h624
              · rcases m.htr 0 4 5 (by decide) (by decide) with h625 | h625
                · rcases m.htr 1 2 3 (by decide) (by decide) with h626 | h626
                  · linarith only [h0, h3, h548, h626, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h628 | h628
                    · linarith only [h0, h405, h628, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h630 | h630
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h631 | h631
                        · linarith only [h3, h548, h631, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h633 | h633
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h634 | h634
                            · linarith only [h0, h3, h548, h630, h634, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                            · linarith only [h0, h3, h630, h634, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                          · linarith only [h624, h633, hc13, hlam, hphi, u3elo0]
                      · linarith only [h3, h547, h630, hc12, hlam, hphi, u2elo2]
                · linarith only [h3, h547, h548, h625, hlam]
              · linarith only [h3, h547, h624, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h641 | h641
            · rcases m.htr 0 3 5 (by decide) (by decide) with h642 | h642
              · rcases m.htr 0 4 5 (by decide) (by decide) with h643 | h643
                · rcases m.htr 1 2 3 (by decide) (by decide) with h644 | h644
                  · linarith only [h0, h3, h644, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h646 | h646
                    · linarith only [h405, h646, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h648 | h648
                      · linarith only [h0, h547, h648, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h650 | h650
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h651 | h651
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h652 | h652
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h653 | h653
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h654 | h654
                                · rcases h0bigk with h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [hlam, p655_0]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    rcases p655_3 (m.d 0 1) (by simp) with h657 | h657
                                    · rcases p655_3 (m.d 0 2) (by simp) with h658 | h658
                                      · linarith only [h0, h658, hlam]
                                      · rcases p655_3 (m.d 0 3) (by simp) with h660 | h660
                                        · linarith only [h1, h660, hlam]
                                        · linarith only [h3, h660, hlam]
                                    · linarith only [h0, h657, hlam]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h1, h650, h654, hc01, hc45, hlam, hphi, ht0b, ht5b, p655_1]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h641, h654, hc01, hc45, hlam, hphi, ht0b, ht5b, p655_1]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    rcases p655_3 (m.d 0 1) (by simp) with h666 | h666
                                    · rcases p655_3 (m.d 0 2) (by simp) with h667 | h667
                                      · linarith only [h0, h667, hlam]
                                      · rcases p655_3 (m.d 0 3) (by simp) with h669 | h669
                                        · linarith only [h1, h669, hlam]
                                        · linarith only [h642, h669, hlam]
                                    · linarith only [h2, h666, hlam]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h0, hlam, p655_0]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [hlam, p655_0]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h3, hlam, p655_0]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h405, hlam, p655_1]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h547, hlam, p655_0]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h1, hlam, p655_1]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht23, p655_1, u3elo0]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [hlam, p655_0]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h3, h641, h654, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p655_1, u3elo2]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h0, h3, h547, hc12, hlam, hphi, ht23, p655_1, u3elo2]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p655_1]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h0, h405, h652, hc12, hlam, hphi, ht23, p655_1, u3elo2]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h641, hlam, p655_0]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [hlam, p655_0]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h0, h405, h547, h652, hc12, hlam, hphi, ht23, p655_1, u3elo2]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h2, hlam, p655_0]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h0, h547, hc12, hlam, hphi, p655_1, u2elo4]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h642, hlam, p655_0]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [h643, hlam, p655_1]
                                  · have p655_0 := h655c.1
                                    have p655_1 := h655c.2.1
                                    have p655_2 := h655c.2.2.1
                                    have p655_3 := h655c.2.2.2
                                    linarith only [hlam, p655_0]
                                · rcases h0bigk with h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [hlam, p693_0]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    rcases p693_3 (m.d 0 1) (by simp) with h695 | h695
                                    · rcases p693_3 (m.d 0 2) (by simp) with h696 | h696
                                      · linarith only [h0, h696, hlam]
                                      · rcases p693_3 (m.d 0 3) (by simp) with h698 | h698
                                        · linarith only [h1, h698, hlam]
                                        · linarith only [h3, h698, hlam]
                                    · linarith only [h0, h695, hlam]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h641, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p693_1]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h643, h654, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p693_1]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h643, h654, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p693_1]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h0, hlam, p693_0]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [hlam, p693_0]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h3, hlam, p693_0]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h405, hlam, p693_1]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h547, hlam, p693_0]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h1, hlam, p693_1]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht23, p693_1, u3elo0]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [hlam, p693_0]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h3, h643, h654, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p693_1, u3elo2]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h0, h3, h547, hc12, hlam, hphi, ht23, p693_1, u3elo2]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p693_1]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h0, h405, h652, hc12, hlam, hphi, ht23, p693_1, u3elo2]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h641, hlam, p693_0]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [hlam, p693_0]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h405, h643, h652, h654, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p693_1, u3elo2]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h2, hlam, p693_0]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h0, h547, h653, hc12, hlam, hphi, ht23, p693_1, u3elo2]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h642, hlam, p693_0]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [h643, hlam, p693_1]
                                  · have p693_0 := h693c.1
                                    have p693_1 := h693c.2.1
                                    have p693_2 := h693c.2.2.1
                                    have p693_3 := h693c.2.2.2
                                    linarith only [hlam, p693_0]
                              · linarith only [h3, h651, h653, hc03, hlam, hphi, u3elo1]
                            · linarith only [h0, h3, h652, hc12, hlam, hphi, ht23, u3elo3]
                          · linarith only [h642, h650, h651, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · linarith only [h3, h641, h650, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h729 | h729
                  · linarith only [h0, h3, h729, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h731 | h731
                    · linarith only [h405, h731, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h733 | h733
                      · linarith only [h0, h547, h733, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h735 | h735
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h736 | h736
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h737 | h737
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h738 | h738
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h739 | h739
                                · linarith only [h1, h643, h735, h739, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases h0bigk with h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [hlam, p741_0]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    rcases p741_3 (m.d 0 1) (by simp) with h743 | h743
                                    · rcases p741_3 (m.d 0 2) (by simp) with h744 | h744
                                      · linarith only [h0, h744, hlam]
                                      · rcases p741_3 (m.d 0 3) (by simp) with h746 | h746
                                        · linarith only [h1, h746, hlam]
                                        · linarith only [h3, h746, hlam]
                                    · linarith only [h0, h743, hlam]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [h1, h736, hc01, hc35, hlam, hphi, ht0b, ht5b, p741_1]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    rcases p741_3 (m.d 0 1) (by simp) with h751 | h751
                                    · rcases p741_3 (m.d 0 2) (by simp) with h752 | h752
                                      · linarith only [h0, h752, hlam]
                                      · rcases p741_3 (m.d 0 3) (by simp) with h754 | h754
                                        · linarith only [h1, h754, hlam]
                                        · linarith only [h641, h754, hlam]
                                    · linarith only [h751, hlam, p741_0]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    rcases p741_3 (m.d 0 1) (by simp) with h758 | h758
                                    · rcases p741_3 (m.d 0 2) (by simp) with h759 | h759
                                      · linarith only [h0, h759, hlam]
                                      · rcases p741_3 (m.d 0 3) (by simp) with h761 | h761
                                        · linarith only [h1, h761, hlam]
                                        · linarith only [h642, h761, hlam]
                                    · linarith only [h2, h758, hlam]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [h0, hlam, p741_0]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [hlam, p741_0]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [h3, hlam, p741_0]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [h405, hlam, p741_1]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [h547, hlam, p741_0]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [h1, hlam, p741_1]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht23, p741_1, u3elo0]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [hlam, p741_0]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [h0, h3, h405, hc12, hlam, hphi, ht23, p741_1, u3elo2]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [h3, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p741_1, u3elo2]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [h643, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p741_1]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [h0, h405, h737, hc12, hlam, hphi, ht23, p741_1, u3elo2]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [h641, hlam, p741_0]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [hlam, p741_0]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [h643, hlam, p741_0]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [h2, hlam, p741_0]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [h0, h547, hc12, hlam, hphi, p741_1, u2elo4]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [h642, hlam, p741_0]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [h3, h642, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p741_1, u3elo2]
                                  · have p741_0 := h741c.1
                                    have p741_1 := h741c.2.1
                                    have p741_2 := h741c.2.2.1
                                    have p741_3 := h741c.2.2.2
                                    linarith only [hlam, p741_0]
                              · linarith only [h0, h3, h738, hc12, hlam, hphi, ht23, u3elo4]
                            · linarith only [h0, h3, h737, hc12, hlam, hphi, ht23, u3elo3]
                          · linarith only [h3, h642, h736, hc13, hlam, hphi, u3elo2]
                        · linarith only [h3, h641, h729, h735, hc12, hlam, hphi, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h789 | h789
                · linarith only [h641, h642, h789, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h791 | h791
                  · linarith only [h0, h3, h791, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h793 | h793
                    · linarith only [h0, h405, h793, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h795 | h795
                      · linarith only [h0, h547, h795, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h797 | h797
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h798 | h798
                          · linarith only [h1, h642, h798, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h800 | h800
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h801 | h801
                              · linarith only [h1, h642, h797, h801, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                              · linarith only [h0, h3, h801, hc12, hlam, hphi, ht23, u3elo4]
                            · linarith only [h0, h3, h800, hc12, hlam, hphi, ht23, u3elo3]
                        · linarith only [h641, h642, h797, hc13, hlam, hphi, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h806 | h806
              · rcases m.htr 0 4 5 (by decide) (by decide) with h807 | h807
                · rcases m.htr 1 2 3 (by decide) (by decide) with h808 | h808
                  · linarith only [h0, h3, h808, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h810 | h810
                    · linarith only [h0, h405, h810, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h812 | h812
                      · linarith only [h0, h547, h812, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h814 | h814
                        · linarith only [h641, h814, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h816 | h816
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h817 | h817
                            · linarith only [h1, h641, h816, h817, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                            · linarith only [h3, h817, hc02, hlam, hphi, ht23, u3elo3]
                          · linarith only [h641, h806, h816, hc13, hlam, hphi, u3elo3]
                · linarith only [h641, h806, h807, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h822 | h822
                · rcases m.htr 1 2 3 (by decide) (by decide) with h823 | h823
                  · linarith only [h0, h3, h823, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h825 | h825
                    · linarith only [h405, h825, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h827 | h827
                      · linarith only [h0, h547, h827, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h829 | h829
                        · linarith only [h1, h641, h829, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h831 | h831
                          · linarith only [h1, h806, h831, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h833 | h833
                            · linarith only [h641, h833, hc03, hlam, hphi, u3elo2]
                            · linarith only [h0, h3, h833, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h836 | h836
                  · linarith only [h0, h3, h836, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h838 | h838
                    · linarith only [h0, h405, h838, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h840 | h840
                      · linarith only [h0, h547, h840, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h842 | h842
                        · linarith only [h1, h641, h842, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h844 | h844
                          · linarith only [h0, h3, h806, h844, hc12, hlam, hphi, ht23, u3elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h846 | h846
                            · linarith only [h0, h3, h641, h846, hc12, hlam, hphi, u2elo2]
                            · linarith only [h0, h3, h846, hc12, hlam, hphi, ht23, u3elo3]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h849 | h849
      · rcases m.htr 0 2 4 (by decide) (by decide) with h850 | h850
        · rcases m.htr 0 2 5 (by decide) (by decide) with h851 | h851
          · linarith only [h0, h2, h851, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h853 | h853
            · rcases m.htr 0 3 5 (by decide) (by decide) with h854 | h854
              · linarith only [h1, h2, h854, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h856 | h856
                · linarith only [h0, h2, h850, h856, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h858 | h858
                  · linarith only [h0, h2, h854, h858, hc23, hlam, hphi, u3elo4]
                  · linarith only [h849, h851, h858, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h861 | h861
              · linarith only [h0, h2, h853, h861, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h863 | h863
                · linarith only [h0, h2, h850, h851, h863, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h865 | h865
                  · linarith only [h0, h2, h861, h865, hc23, hlam, hphi, u3elo4]
                  · linarith only [h849, h851, h865, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h868 | h868
          · linarith only [h0, h2, h850, h868, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h870 | h870
            · linarith only [h849, h850, h870, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h872 | h872
              · linarith only [h0, h2, h849, h850, h872, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h874 | h874
                · rcases m.htr 1 2 3 (by decide) (by decide) with h875 | h875
                  · linarith only [h0, h2, h870, h874, h875, hc23, hlam, hphi, u3elo3]
                  · linarith only [h849, h850, h875, hc12, hlam, hphi, u2elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h878 | h878
                  · linarith only [h0, h2, h872, h878, hc23, hlam, hphi, u3elo4]
                  · linarith only [h849, h850, h878, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h881 | h881
        · rcases m.htr 0 2 5 (by decide) (by decide) with h882 | h882
          · linarith only [h0, h2, h882, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h884 | h884
            · rcases m.htr 0 3 5 (by decide) (by decide) with h885 | h885
              · linarith only [h1, h2, h885, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h887 | h887
                · linarith only [h0, h2, h849, h881, h885, h887, hc12, hlam, hphi, ht23, u3elo4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h889 | h889
                  · linarith only [h0, h849, h885, h889, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h891 | h891
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h892 | h892
                      · linarith only [h1, h2, h882, h889, h892, hlam]
                      · linarith only [h1, h2, h889, h891, h892, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · linarith only [h849, h881, h891, hc12, hlam, hphi, u2elo2]
            · linarith only [h849, h881, h884, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h897 | h897
          · linarith only [h0, h2, h881, h897, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h899 | h899
            · rcases m.htr 0 3 5 (by decide) (by decide) with h900 | h900
              · linarith only [h1, h2, h900, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h902 | h902
                · linarith only [h0, h2, h899, h900, h902, hc12, hlam, hphi, ht23, u3elo4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h904 | h904
                  · linarith only [h0, h881, h899, h900, h904, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h906 | h906
                    · linarith only [h0, h881, h906, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h908 | h908
                      · linarith only [h1, h2, h897, h904, h908, hlam]
                      · linarith only [h1, h2, h904, h908, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h911 | h911
              · linarith only [h0, h2, h899, h911, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h913 | h913
                · rcases m.htr 1 2 3 (by decide) (by decide) with h914 | h914
                  · linarith only [h0, h849, h899, h914, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h916 | h916
                    · linarith only [h1, h2, h881, h913, h914, h916, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h918 | h918
                      · linarith only [h1, h2, h897, h899, h913, h914, h918, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h0, h2, h918, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h921 | h921
                  · linarith only [h0, h849, h921, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h923 | h923
                    · linarith only [h0, h881, h923, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h925 | h925
                      · linarith only [h1, h2, h897, h911, h921, h925, hc02, hlam, hphi, ht23, u3elo4]
                      · linarith only [h0, h2, h925, hc12, hlam, hphi, u2elo4]
  · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

end R2N4
