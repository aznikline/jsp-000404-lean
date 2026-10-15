import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_R_L_0_L_I_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h0emin := hb0.2.2
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h5, h7, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · rcases h0emin with h11 | h11 | h11 | h11 | h11
                      · rcases h3bigk with h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [hlam, p12_0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h2, h5, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h2, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          rcases p12_3 (m.d 0 3) (by simp) with h16 | h16
                          · rcases p12_3 (m.d 1 3) (by simp) with h17 | h17
                            · linarith only [h1, h17, hlam]
                            · linarith only [h17, h6, hlam]
                          · linarith only [h16, hlam, p12_0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          rcases p12_3 (m.d 0 3) (by simp) with h21 | h21
                          · rcases p12_3 (m.d 1 3) (by simp) with h22 | h22
                            · linarith only [h1, h22, hlam]
                            · linarith only [h22, h5, h8, hlam]
                          · linarith only [h21, hlam, p12_0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h1, hlam, p12_0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [hlam, p12_0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h1, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12_1]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          rcases p12_3 (m.d 0 3) (by simp) with h29 | h29
                          · rcases p12_3 (m.d 1 3) (by simp) with h30 | h30
                            · rcases p12_3 (m.d 2 3) (by simp) with h31 | h31
                              · linarith only [h31, h5, hlam]
                              · linarith only [h31, h7, hlam]
                            · linarith only [h30, hlam, p12_0]
                          · linarith only [h29, h3, hlam]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          rcases p12_3 (m.d 0 3) (by simp) with h36 | h36
                          · rcases p12_3 (m.d 1 3) (by simp) with h37 | h37
                            · rcases p12_3 (m.d 2 3) (by simp) with h38 | h38
                              · linarith only [h38, h5, hlam]
                              · linarith only [h38, h8, hlam]
                            · linarith only [h37, hlam, p12_0]
                          · linarith only [h36, h4, hlam]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h2, hlam, p12_0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h5, hlam, p12_0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [hlam, p12_0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h0, h5, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h3, hlam, p12_0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h6, hlam, p12_0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h7, hlam, p12_0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [hlam, p12_0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h9, hlam, p12_1]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h4, hlam, p12_0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [hc13, hlam, hphi, ht34, ht45, p12_1, u5elo3]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h8, hlam, p12_0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h0, h5, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [hlam, p12_0]
                      · linarith only [h11, hlam, ht01, ht12, u2elo0]
                      · linarith only [h11, h2, hlam, ht01, ht12, u2elo0]
                      · linarith only [h11, h2, h3, hlam, ht01, ht12, u2elo0]
                      · linarith only [h11, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                  · linarith only [h2, h4, h7, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h63 | h63
                  · linarith only [h1, h6, h63, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h65 | h65
                    · rcases h0emin with h66 | h66 | h66 | h66 | h66
                      · rcases h3bigk with h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h2, h6, h63, h65, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p67_1, u2elo0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          rcases p67_3 (m.d 0 3) (by simp) with h70 | h70
                          · rcases p67_3 (m.d 1 3) (by simp) with h71 | h71
                            · linarith only [h1, h71, hlam]
                            · linarith only [h5, h71, hlam]
                          · linarith only [h2, h70, hlam]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h2, h63, h65, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p67_1, u2elo0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h2, h63, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p67_1, u2elo0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h1, hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          rcases p67_3 (m.d 0 3) (by simp) with h79 | h79
                          · rcases p67_3 (m.d 1 3) (by simp) with h80 | h80
                            · rcases p67_3 (m.d 2 3) (by simp) with h81 | h81
                              · linarith only [h5, h81, hlam]
                              · rcases p67_3 (m.d 3 4) (by simp) with h83 | h83
                                · linarith only [h6, h83, hlam]
                                · linarith only [h7, h83, hlam]
                            · linarith only [h5, h80, hlam]
                          · linarith only [h2, h79, hlam]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h1, h63, h65, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p67_1]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h1, h2, h63, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p67_1, u2elo0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h2, hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h5, hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h7, hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h63, hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h3, hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h6, hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h2, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p67_1, u2elo0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h1, h2, h6, h63, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p67_1, u2elo0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h4, hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h6, h65, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p67_1]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p67_1, u2elo0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h65, hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [hlam, p67_0]
                      · linarith only [h66, hlam, ht01, ht12, u2elo0]
                      · linarith only [h2, h66, hlam, ht01, ht12, u2elo0]
                      · linarith only [h2, h3, h66, hlam, ht01, ht12, u2elo0]
                      · linarith only [h66, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                    · linarith only [h65, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h110 | h110
                · linarith only [h110, h2, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h112 | h112
                  · linarith only [h112, h2, h3, h5, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h114 | h114
                    · rcases h0emin with h115 | h115 | h115 | h115 | h115
                      · rcases h3bigk with h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          rcases p116_3 (m.d 0 3) (by simp) with h118 | h118
                          · rcases p116_3 (m.d 1 3) (by simp) with h119 | h119
                            · linarith only [h1, h119, hlam]
                            · rcases p116_3 (m.d 2 3) (by simp) with h121 | h121
                              · linarith only [h121, h2, hlam]
                              · rcases p116_3 (m.d 3 4) (by simp) with h123 | h123
                                · linarith only [h123, h3, hlam]
                                · linarith only [h123, h6, hlam]
                          · linarith only [h1, h118, hlam]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          rcases p116_3 (m.d 0 3) (by simp) with h127 | h127
                          · rcases p116_3 (m.d 1 3) (by simp) with h128 | h128
                            · linarith only [h1, h128, hlam]
                            · linarith only [h128, h5, hlam]
                          · linarith only [h127, h2, hlam]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h2, h5, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p116_1, u2elo0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h112, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p116_1, u2elo0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h1, hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h6, hc23, hc34, hlam, hphi, p116_1]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h6, hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h112, h2, h3, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p116_1, u2elo0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h2, hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h5, hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h110, hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h112, hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h3, hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h2, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p116_1, u2elo0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h2, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p116_1, u2elo0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h112, h2, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p116_1, u2elo0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h4, hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h5, hc23, hlam, hphi, ht34, ht45, p116_1, u5elo3]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p116_1, u2elo0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h114, hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [hlam, p116_0]
                      · linarith only [h115, hlam, ht01, ht12, u2elo0]
                      · linarith only [h115, h2, hlam, ht01, ht12, u2elo0]
                      · linarith only [h115, h2, h3, hlam, ht01, ht12, u2elo0]
                      · linarith only [h115, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                    · linarith only [h114, h5, h6, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h2, h5, hc12, hlam, hphi, u2elo0]
          · linarith only [h3, h4, hc34, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h161 | h161
          · rcases m.htr 1 2 3 (by decide) (by decide) with h162 | h162
            · rcases m.htr 1 3 4 (by decide) (by decide) with h163 | h163
              · linarith only [h161, h163, h3, hc13, hlam, hphi, ht01, u0ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                · linarith only [h161, h165, h3, hlam, hphi, ht01, ht12, u0ehi4, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h167 | h167
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h168 | h168
                    · rcases h0emin with h169 | h169 | h169 | h169 | h169
                      · rcases h3bigk with h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [hlam, p170_0]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [h3, hc13, hc34, hlam, hphi, p170_1]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [h3, hc23, hc34, hlam, hphi, p170_1]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [h3, hlam, p170_0]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          rcases p170_3 (m.d 0 3) (by simp) with h175 | h175
                          · rcases p170_3 (m.d 1 3) (by simp) with h176 | h176
                            · linarith only [h1, h176, hlam]
                            · linarith only [h162, h167, h176, hlam]
                          · linarith only [h175, hlam, p170_0]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [h1, hlam, p170_0]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [hlam, p170_0]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [h1, h167, h168, hc01, hc45, hlam, hphi, ht0b, ht5b, p170_1]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [h163, hlam, p170_0]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          rcases p170_3 (m.d 0 3) (by simp) with h184 | h184
                          · rcases p170_3 (m.d 1 3) (by simp) with h185 | h185
                            · rcases p170_3 (m.d 2 3) (by simp) with h186 | h186
                              · linarith only [h162, h186, hlam]
                              · linarith only [h167, h186, hlam]
                            · linarith only [h185, hlam, p170_0]
                          · linarith only [h161, h184, hlam]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [h2, hlam, p170_0]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [h162, hlam, p170_0]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [hlam, p170_0]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [h165, hlam, p170_0]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [h168, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p170_1, u2elo0]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p170_1, u0ehi2]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          rcases p170_3 (m.d 0 3) (by simp) with h197 | h197
                          · linarith only [h197, h3, hlam]
                          · linarith only [h1, h197, hlam]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          rcases p170_3 (m.d 0 3) (by simp) with h200 | h200
                          · linarith only [h200, h3, hlam]
                          · linarith only [h2, h200, hlam]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [hlam, p170_0]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          rcases p170_3 (m.d 0 3) (by simp) with h204 | h204
                          · linarith only [h204, h3, hlam]
                          · linarith only [h161, h204, hlam]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [h161, hlam, p170_0]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [h162, h167, hlam, p170_1]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [h167, hlam, p170_0]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [h168, hlam, p170_0]
                        · have p170_0 := h170c.1
                          have p170_1 := h170c.2.1
                          have p170_2 := h170c.2.2.1
                          have p170_3 := h170c.2.2.2
                          linarith only [hlam, p170_0]
                      · linarith only [h169, hlam, ht01, ht12, u2elo0]
                      · linarith only [h169, h2, hlam, ht01, ht12, u2elo0]
                      · rcases h3bigk with h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [hlam, p214_0]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [h3, hc13, hc34, hlam, hphi, p214_1]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [h167, h3, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p214_1]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [h3, hlam, p214_0]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          rcases p214_3 (m.d 0 3) (by simp) with h219 | h219
                          · rcases p214_3 (m.d 1 3) (by simp) with h220 | h220
                            · linarith only [h1, h220, hlam]
                            · linarith only [h162, h167, h220, hlam]
                          · linarith only [h219, hlam, p214_0]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [h1, hlam, p214_0]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [hlam, p214_0]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [h1, h167, h168, hc01, hc45, hlam, hphi, ht0b, ht5b, p214_1]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [h163, hlam, p214_0]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          rcases p214_3 (m.d 0 3) (by simp) with h228 | h228
                          · rcases p214_3 (m.d 1 3) (by simp) with h229 | h229
                            · rcases p214_3 (m.d 2 3) (by simp) with h230 | h230
                              · linarith only [h162, h230, hlam]
                              · linarith only [h167, h230, hlam]
                            · linarith only [h229, hlam, p214_0]
                          · linarith only [h161, h228, hlam]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [h2, hlam, p214_0]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [h162, hlam, p214_0]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [hlam, p214_0]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [h165, hlam, p214_0]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [h168, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p214_1, u2elo0]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p214_1, u0ehi2]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          rcases p214_3 (m.d 0 3) (by simp) with h241 | h241
                          · linarith only [h241, h3, hlam]
                          · linarith only [h1, h241, hlam]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          rcases p214_3 (m.d 0 3) (by simp) with h244 | h244
                          · linarith only [h244, h3, hlam]
                          · linarith only [h2, h244, hlam]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [hlam, p214_0]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          rcases p214_3 (m.d 0 3) (by simp) with h248 | h248
                          · linarith only [h248, h3, hlam]
                          · linarith only [h161, h248, hlam]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [h161, hlam, p214_0]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [h162, h167, hlam, p214_1]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [h167, hlam, p214_0]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [h168, hlam, p214_0]
                        · have p214_0 := h214c.1
                          have p214_1 := h214c.2.1
                          have p214_2 := h214c.2.2.1
                          have p214_3 := h214c.2.2.2
                          linarith only [hlam, p214_0]
                      · linarith only [h169, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                    · linarith only [h168, h3, hc03, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h161, h167, h3, hc23, hc34, hlam, hphi]
            · linarith only [h162, h2, hc12, hlam, hphi, u2elo0]
          · linarith only [h161, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h262 | h262
      · linarith only [h0, h1, h262, hlam]
      · linarith only [h262, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]

theorem r1l7_10_12_13_25_L_R_L_I_L_R_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h5, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h9, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
              · linarith only [h4, h6, hlam, hphi, ht34, ht45, u3ehi1, u5elo2]
            · linarith only [h0, h2, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15 | h15
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                · linarith only [h0, h1, h14, h16, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h14, h16, h4, hlam]
              · linarith only [h14, h15, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h20 | h20
              · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h1, h14, h20, h21, h22, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h14, h21, h22, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                  · linarith only [h21, h25, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h25, h4, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h31 | h31
                      · rcases h2bigk with h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          rcases p32_3 (m.d 0 2) (by simp) with h34 | h34
                          · rcases p32_3 (m.d 1 2) (by simp) with h35 | h35
                            · linarith only [h0, h35, hlam]
                            · rcases p32_3 (m.d 2 3) (by simp) with h37 | h37
                              · linarith only [h1, h37, hlam]
                              · linarith only [h37, h4, hlam]
                          · linarith only [h0, h34, hlam]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h0, h28, h31, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p32_1, u3ehi4]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          rcases p32_3 (m.d 0 2) (by simp) with h42 | h42
                          · rcases p32_3 (m.d 1 2) (by simp) with h43 | h43
                            · linarith only [h0, h43, hlam]
                            · rcases p32_3 (m.d 2 3) (by simp) with h45 | h45
                              · linarith only [h1, h45, hlam]
                              · linarith only [h28, h45, hlam]
                          · linarith only [h42, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          rcases p32_3 (m.d 0 2) (by simp) with h49 | h49
                          · rcases p32_3 (m.d 1 2) (by simp) with h50 | h50
                            · linarith only [h0, h50, hlam]
                            · rcases p32_3 (m.d 2 3) (by simp) with h52 | h52
                              · linarith only [h1, h52, hlam]
                              · linarith only [h29, h52, hlam]
                          · linarith only [h49, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h0, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h4, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h14, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h20, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h1, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          rcases p32_3 (m.d 0 2) (by simp) with h62 | h62
                          · rcases p32_3 (m.d 1 2) (by simp) with h63 | h63
                            · linarith only [h63, hlam, p32_0]
                            · rcases p32_3 (m.d 2 3) (by simp) with h65 | h65
                              · rcases p32_3 (m.d 2 4) (by simp) with h66 | h66
                                · linarith only [h28, h66, hlam]
                                · linarith only [h14, h66, hlam]
                              · linarith only [h65, hlam, p32_0]
                          · linarith only [h0, h62, hlam]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h20, h30, hc12, hc23, hlam, hphi, p32_1]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h0, h1, h20, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p32_1]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h2, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          rcases p32_3 (m.d 0 2) (by simp) with h75 | h75
                          · rcases p32_3 (m.d 1 2) (by simp) with h76 | h76
                            · linarith only [h76, hlam, p32_0]
                            · rcases p32_3 (m.d 2 3) (by simp) with h78 | h78
                              · rcases p32_3 (m.d 2 4) (by simp) with h79 | h79
                                · rcases p32_3 (m.d 2 5) (by simp) with h80 | h80
                                  · linarith only [h30, h80, hlam]
                                  · linarith only [h20, h80, hlam]
                                · linarith only [h79, hlam, p32_0]
                              · linarith only [h4, h78, hlam]
                          · linarith only [h0, h75, hlam]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h28, hlam, p32_1]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h20, hc12, hc24, hlam, hphi, p32_1]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h3, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p32_1, u5elo2]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h29, hlam, p32_1]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [h30, hlam, p32_0]
                        · have p32_0 := h32c.1
                          have p32_1 := h32c.2.1
                          have p32_2 := h32c.2.2.1
                          have p32_3 := h32c.2.2.2
                          linarith only [hlam, p32_0]
                      · linarith only [h31, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h14, h30, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h29, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h97 | h97
                  · linarith only [h28, h97, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h97, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
        · linarith only [h1, h3, hlam, hphi, ht34, ht45, u3ehi0, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h101 | h101
        · rcases m.htr 1 2 3 (by decide) (by decide) with h102 | h102
          · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
            · linarith only [h0, h103, h2, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
              · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                · linarith only [h0, h102, h106, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h102, h106, h2, hc34, hlam, hphi, u3ehi2]
              · linarith only [h102, h105, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
          · linarith only [h1, h102, h2, hc12, hc24, hlam, hphi]
        · linarith only [h1, h101, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h112 | h112
      · rcases m.htr 0 2 5 (by decide) (by decide) with h113 | h113
        · rcases m.htr 1 2 3 (by decide) (by decide) with h114 | h114
          · linarith only [h1, h112, h114, hc12, hlam, hphi, ht01, u0ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h116 | h116
            · rcases m.htr 1 2 5 (by decide) (by decide) with h117 | h117
              · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                · rcases m.htr 2 3 5 (by decide) (by decide) with h119 | h119
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h120 | h120
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h121 | h121
                      · rcases h2bigk with h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h116, h119, h120, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p122_1, u3ehi4]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h1, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h1, h119, h120, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p122_1, u3ehi4]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h1, h119, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p122_1, u3ehi4]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h0, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h114, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h0, h119, h120, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p122_1, u3ehi4]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h0, h1, h119, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p122_1, u3ehi4]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hc23, hlam, hphi, ht01, ht12, p122_1, u0ehi1]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h116, h119, h120, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p122_1, u3ehi4]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          rcases p122_3 (m.d 0 2) (by simp) with h136 | h136
                          · linarith only [h1, h136, hlam]
                          · linarith only [h112, h136, hlam]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          rcases p122_3 (m.d 0 2) (by simp) with h139 | h139
                          · linarith only [h1, h139, hlam]
                          · linarith only [h113, h139, hlam]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h112, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h116, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h118, hlam, p122_1]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h0, h116, h119, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p122_1, u3ehi4]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h113, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h117, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h119, hlam, p122_1]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h120, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hlam, p122_0]
                      · linarith only [h121, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h118, h120, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                  · linarith only [h1, h119, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · linarith only [h1, h112, h118, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
              · linarith only [h116, h117, hc24, hlam, hphi, ht45, u5elo2]
            · linarith only [h1, h112, h116, hc12, hc23, hlam, hphi]
        · linarith only [h112, h113, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h159 | h159
        · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
          · linarith only [h1, h159, h160, hc12, hlam, hphi, ht01, u0ehi4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h162 | h162
            · linarith only [h0, h112, h162, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h164 | h164
              · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                · rcases m.htr 2 3 5 (by decide) (by decide) with h166 | h166
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h167 | h167
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h168 | h168
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
                          linarith only [h112, h164, h165, h166, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p169_1, u3ehi4]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h1, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h112, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h112, h165, h166, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p169_1, u3ehi4]
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
                          linarith only [h160, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h162, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h0, h166, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p169_1, u3ehi4]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [hc23, hlam, hphi, ht01, ht12, p169_1, u0ehi1]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h164, h166, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p169_1, u3ehi4]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h112, h159, h166, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p169_1, u3ehi4]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          rcases p169_3 (m.d 0 2) (by simp) with h184 | h184
                          · linarith only [h1, h184, hlam]
                          · linarith only [h159, h184, hlam]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h0, h164, h166, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p169_1, u3ehi4]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h164, h166, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p169_1, u3ehi4]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h165, hlam, p169_1]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          rcases p169_3 (m.d 0 2) (by simp) with h191 | h191
                          · linarith only [h112, h191, hlam]
                          · linarith only [h159, h191, hlam]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h159, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h164, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h166, hlam, p169_1]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h167, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [hlam, p169_0]
                      · linarith only [h168, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h0, h112, h164, h166, h167, hlam, hphi, ht34, ht45, u3ehi4, u5elo4]
                  · linarith only [h1, h166, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
                · linarith only [h1, h165, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
              · linarith only [h1, h159, h164, hc12, hc23, hlam, hphi]
        · linarith only [h159, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h205 | h205
    · rcases m.htr 0 2 4 (by decide) (by decide) with h206 | h206
      · rcases m.htr 0 2 5 (by decide) (by decide) with h207 | h207
        · rcases m.htr 1 2 3 (by decide) (by decide) with h208 | h208
          · rcases m.htr 1 2 4 (by decide) (by decide) with h209 | h209
            · rcases m.htr 1 2 5 (by decide) (by decide) with h210 | h210
              · rcases m.htr 2 3 4 (by decide) (by decide) with h211 | h211
                · rcases m.htr 2 3 5 (by decide) (by decide) with h212 | h212
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h213 | h213
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h214 | h214
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
                          linarith only [h0, hlam, p215_1]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [h211, h214, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p215_1, u3ehi4]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          rcases p215_3 (m.d 0 2) (by simp) with h219 | h219
                          · rcases p215_3 (m.d 1 2) (by simp) with h220 | h220
                            · rcases p215_3 (m.d 2 3) (by simp) with h221 | h221
                              · linarith only [h205, h221, hlam]
                              · linarith only [h211, h221, hlam]
                            · linarith only [h209, h220, hlam]
                          · linarith only [h219, hlam, p215_0]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          rcases p215_3 (m.d 0 2) (by simp) with h226 | h226
                          · rcases p215_3 (m.d 1 2) (by simp) with h227 | h227
                            · rcases p215_3 (m.d 2 3) (by simp) with h228 | h228
                              · linarith only [h205, h228, hlam]
                              · linarith only [h212, h228, hlam]
                            · linarith only [h210, h227, hlam]
                          · linarith only [h226, hlam, p215_0]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p215_1, u0ehi1]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [hlam, p215_0]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [h211, h214, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p215_1, u3ehi4]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          rcases p215_3 (m.d 0 2) (by simp) with h236 | h236
                          · linarith only [h0, h236, hlam]
                          · linarith only [h206, h236, hlam]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          rcases p215_3 (m.d 0 2) (by simp) with h239 | h239
                          · linarith only [h0, h239, hlam]
                          · linarith only [h207, h239, hlam]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [h205, hlam, p215_0]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [h208, hlam, p215_0]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [hlam, p215_0]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [h205, h211, h214, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p215_1, u3ehi4]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [h0, h205, h212, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p215_1, u3ehi4]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [h206, hlam, p215_0]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [h209, hlam, p215_0]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [h211, hlam, p215_1]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [hlam, p215_0]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [h0, h206, h212, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p215_1, u3ehi4]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [h207, hlam, p215_0]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [h210, hlam, p215_0]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [h212, hlam, p215_1]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [h213, hlam, p215_0]
                        · have p215_0 := h215c.1
                          have p215_1 := h215c.2.1
                          have p215_2 := h215c.2.2.1
                          have p215_3 := h215c.2.2.2
                          linarith only [hlam, p215_0]
                      · linarith only [h214, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h211, h213, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                  · linarith only [h212, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h260 | h260
                  · linarith only [h211, h260, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h260, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
              · linarith only [h0, h210, hc25, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h209, hc24, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h205, h208, hc02, hlam, hphi, u0ehi0]
        · linarith only [h207, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h267 | h267
        · rcases m.htr 1 2 3 (by decide) (by decide) with h268 | h268
          · rcases m.htr 1 2 4 (by decide) (by decide) with h269 | h269
            · linarith only [h205, h206, h269, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h269, hc24, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h205, h268, hc02, hlam, hphi, u0ehi0]
        · linarith only [h205, h267, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h274 | h274
      · rcases m.htr 0 2 5 (by decide) (by decide) with h275 | h275
        · rcases m.htr 1 2 3 (by decide) (by decide) with h276 | h276
          · linarith only [h0, h205, h276, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h0, h276, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h0, h275, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h280 | h280
        · rcases m.htr 1 2 3 (by decide) (by decide) with h281 | h281
          · linarith only [h0, h205, h281, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h0, h281, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h0, h280, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo2]

end R2N4
