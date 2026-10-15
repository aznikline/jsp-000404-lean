import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_23_L_I_L_R_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
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
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                                    · linarith only [h0, h10, h14, h17, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                    · linarith only [h0, h10, h14, h16, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h16, h7, h9, hlam, hphi, ht23, u2ehi3, u3elo0]
                                · linarith only [h15, hlam, hphi, ht23, u2ehi2, u3elo4]
                              · linarith only [h14, hlam, hphi, ht23, u2ehi2, u3elo3]
                            · linarith only [h13, h7, hc13, hlam, hphi, u3elo0]
                          · linarith only [h12, h6, h7, h9, hlam, hphi, ht23, u2ehi1, u3elo0]
                        · linarith only [h10, h11, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h10, hlam, hphi, ht23, u2ehi1, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h32 | h32
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                                  · linarith only [h2, h28, h33, h9, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h35 | h35
                                    · linarith only [h0, h27, h31, h35, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases h0bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        linarith only [hlam, p37_0]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        linarith only [h0, h27, h32, h35, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p37_1]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        rcases p37_3 (m.d 0 1) (by simp) with h40 | h40
                                        · rcases p37_3 (m.d 0 2) (by simp) with h41 | h41
                                          · linarith only [h0, h41, hlam]
                                          · linarith only [h4, h41, hlam]
                                        · linarith only [h1, h40, hlam]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        rcases p37_3 (m.d 0 1) (by simp) with h45 | h45
                                        · rcases p37_3 (m.d 0 2) (by simp) with h46 | h46
                                          · linarith only [h0, h46, hlam]
                                          · linarith only [h46, h5, hlam]
                                        · linarith only [h2, h45, hlam]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        rcases p37_3 (m.d 0 1) (by simp) with h50 | h50
                                        · rcases p37_3 (m.d 0 2) (by simp) with h51 | h51
                                          · linarith only [h0, h51, hlam]
                                          · linarith only [h51, h6, hlam]
                                        · linarith only [h3, h50, hlam]
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
                                        rcases p37_3 (m.d 0 1) (by simp) with h57 | h57
                                        · rcases p37_3 (m.d 0 2) (by simp) with h58 | h58
                                          · rcases p37_3 (m.d 0 3) (by simp) with h59 | h59
                                            · linarith only [h4, h59, hlam]
                                            · rcases p37_3 (m.d 0 4) (by simp) with h61 | h61
                                              · linarith only [h5, h61, hlam]
                                              · rcases p37_3 (m.d 0 5) (by simp) with h63 | h63
                                                · linarith only [h6, h63, hlam]
                                                · rcases h3bigk with h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [hlam, p65_0]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h0, h27, h32, h33, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p37_1, p65_1, u2ehi3]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h0, h32, h33, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p37_1, p65_1, u2ehi3]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h0, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p37_1, p65_1]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h0, h35, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p37_1, p65_1]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h1, hlam, p65_0]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [hlam, p65_0]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h32, h33, hlam, hphi, ht23, p65_1, u2ehi3, u3elo1]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h0, h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p37_1, p65_1]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h0, h1, h35, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p37_1, p65_1]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h4, hlam, p65_0]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h27, hlam, p65_0]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [hlam, p65_0]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h0, h27, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p65_1]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h0, h1, h27, h35, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p37_1, p65_1]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h7, hlam, p65_0]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h30, hlam, p65_0]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h31, hlam, p65_0]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [hlam, p65_0]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h35, hlam, p65_1]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h8, hlam, p65_0]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [hc13, hlam, hphi, p65_1, u3elo4]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h32, hlam, p65_0]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [h27, h32, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p65_1, u3elo1]
                                                  · have p65_0 := h65c.1
                                                    have p65_1 := h65c.2.1
                                                    have p65_2 := h65c.2.2.1
                                                    have p65_3 := h65c.2.2.2
                                                    linarith only [hlam, p65_0]
                                          · linarith only [h4, h58, hlam]
                                        · linarith only [h1, h57, hlam]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        rcases p37_3 (m.d 0 1) (by simp) with h93 | h93
                                        · rcases p37_3 (m.d 0 2) (by simp) with h94 | h94
                                          · rcases p37_3 (m.d 0 3) (by simp) with h95 | h95
                                            · linarith only [h4, h95, hlam]
                                            · linarith only [h7, h95, hlam]
                                          · linarith only [h5, h94, hlam]
                                        · linarith only [h2, h93, hlam]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        rcases p37_3 (m.d 0 1) (by simp) with h100 | h100
                                        · rcases p37_3 (m.d 0 2) (by simp) with h101 | h101
                                          · rcases p37_3 (m.d 0 3) (by simp) with h102 | h102
                                            · linarith only [h102, h4, hlam]
                                            · linarith only [h102, h8, hlam]
                                          · linarith only [h101, h6, hlam]
                                        · linarith only [h100, h3, hlam]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        linarith only [h1, hlam, p37_1]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        linarith only [h4, hlam, p37_1]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        linarith only [hlam, p37_0]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        linarith only [h2, h28, hlam, hphi, ht23, p37_1, u2ehi3, u3elo0]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        linarith only [h2, h28, h9, hlam, hphi, ht23, p37_1, u2ehi3, u3elo0]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        linarith only [h2, hlam, p37_0]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        linarith only [h5, hlam, p37_0]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        linarith only [h7, hlam, p37_0]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        linarith only [hlam, p37_0]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        linarith only [h9, hlam, p37_0]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        linarith only [h3, hlam, p37_0]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        linarith only [h6, hlam, p37_1]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        linarith only [h8, hlam, p37_0]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        linarith only [h2, h28, h8, hlam, hphi, ht23, p37_1, u2ehi3, u3elo0]
                                      · have p37_0 := h37c.1
                                        have p37_1 := h37c.2.1
                                        have p37_2 := h37c.2.2.1
                                        have p37_3 := h37c.2.2.2
                                        linarith only [hlam, p37_0]
                                · linarith only [h32, hlam, hphi, ht23, u2ehi2, u3elo4]
                              · linarith only [h31, hlam, hphi, ht23, u2ehi2, u3elo3]
                            · linarith only [h30, h7, hc13, hlam, hphi, u3elo0]
                          · linarith only [h29, h6, h8, hlam, hphi, ht23, u2ehi1, u3elo0]
                        · linarith only [h27, h28, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h27, hlam, hphi, ht23, u2ehi1, u3elo2]
                  · linarith only [h4, h8, hlam, hphi, ht23, u2ehi2, u3elo4]
                · linarith only [h4, h7, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h4, h6, hc25, hlam, hphi, u2ehi2]
            · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
          · linarith only [h4, hlam, hphi, ht23, u2ehi0, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h133 | h133
          · rcases m.htr 0 2 4 (by decide) (by decide) with h134 | h134
            · rcases m.htr 0 2 5 (by decide) (by decide) with h135 | h135
              · linarith only [h0, h135, h3, hlam]
              · linarith only [h133, h135, hc25, hlam, hphi, u2ehi2]
            · linarith only [h133, h134, hc24, hlam, hphi, u2ehi2]
          · linarith only [h133, hlam, hphi, ht23, u2ehi0, u3elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h140 | h140
        · rcases m.htr 0 2 3 (by decide) (by decide) with h141 | h141
          · rcases m.htr 0 2 4 (by decide) (by decide) with h142 | h142
            · linarith only [h0, h142, h2, hlam]
            · linarith only [h141, h142, hc24, hlam, hphi, u2ehi2]
          · linarith only [h141, hlam, hphi, ht23, u2ehi0, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h146 | h146
          · rcases m.htr 0 2 4 (by decide) (by decide) with h147 | h147
            · linarith only [h0, h147, h2, hlam]
            · linarith only [h146, h147, hc24, hlam, hphi, u2ehi2]
          · linarith only [h146, hlam, hphi, ht23, u2ehi0, u3elo2]
    · linarith only [h0, h1, hlam, hphi, ht23, u2ehi1, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h152 | h152
    · rcases m.htr 0 1 4 (by decide) (by decide) with h153 | h153
      · rcases m.htr 0 1 5 (by decide) (by decide) with h154 | h154
        · rcases m.htr 0 2 3 (by decide) (by decide) with h155 | h155
          · rcases m.htr 0 2 4 (by decide) (by decide) with h156 | h156
            · rcases m.htr 0 2 5 (by decide) (by decide) with h157 | h157
              · rcases m.htr 0 3 4 (by decide) (by decide) with h158 | h158
                · rcases m.htr 0 3 5 (by decide) (by decide) with h159 | h159
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h160 | h160
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h161 | h161
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h162 | h162
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h163 | h163
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h164 | h164
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h166 | h166
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h167 | h167
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h168 | h168
                                    · linarith only [h0, h152, h161, h165, h168, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h0, h152, h162, h164, h167, h168, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h158, h160, h167, hlam, hphi, ht23, u2ehi3, u3elo0]
                                · linarith only [h165, h166, hlam, hphi, ht23, u2ehi3, u3elo4]
                              · linarith only [h165, hlam, hphi, ht23, u2ehi2, u3elo3]
                            · linarith only [h158, h164, hc13, hlam, hphi, u3elo0]
                          · linarith only [h0, h152, h161, h163, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h0, h152, h161, h162, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h0, h161, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h178 | h178
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h179 | h179
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h180 | h180
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h181 | h181
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h182 | h182
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h183 | h183
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h184 | h184
                                  · linarith only [h0, h152, h160, h179, h181, h184, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h186 | h186
                                    · linarith only [h0, h152, h160, h178, h182, h186, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · rcases h0bigk with h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [hlam, p188_0]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [h0, hlam, p188_1]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [h0, h152, h178, h183, h186, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p188_1]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [h0, h153, h179, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p188_1, u2ehi3]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [h0, h157, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p188_1, u2ehi4]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [h0, h152, h178, h183, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p188_1, u2ehi4]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [hlam, p188_0]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        rcases p188_3 (m.d 0 1) (by simp) with h196 | h196
                                        · linarith only [h0, h196, hlam]
                                        · linarith only [h152, h196, hlam]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        rcases p188_3 (m.d 0 1) (by simp) with h199 | h199
                                        · linarith only [h0, h199, hlam]
                                        · linarith only [h153, h199, hlam]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        rcases p188_3 (m.d 0 1) (by simp) with h202 | h202
                                        · linarith only [h0, h202, hlam]
                                        · linarith only [h154, h202, hlam]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [h152, hlam, p188_1]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [h155, hlam, p188_1]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [hlam, p188_0]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [h153, h179, hlam, hphi, ht23, p188_1, u2ehi3, u3elo0]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [h153, h160, h179, hlam, hphi, ht23, p188_1, u2ehi3, u3elo0]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [h153, hlam, p188_0]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [h156, hlam, p188_0]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [h158, hlam, p188_0]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [hlam, p188_0]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [h160, hlam, p188_0]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [h154, hlam, p188_0]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [h157, hlam, p188_1]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [h159, hlam, p188_0]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [h0, h153, h154, h179, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p188_1, u2ehi3]
                                      · have p188_0 := h188c.1
                                        have p188_1 := h188c.2.1
                                        have p188_2 := h188c.2.2.1
                                        have p188_3 := h188c.2.2.2
                                        linarith only [hlam, p188_0]
                                · linarith only [h183, hlam, hphi, ht23, u2ehi2, u3elo4]
                              · linarith only [h182, hlam, hphi, ht23, u2ehi2, u3elo3]
                            · linarith only [h158, h181, hc13, hlam, hphi, u3elo0]
                          · linarith only [h0, h152, h178, h180, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h0, h152, h178, h179, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h0, h152, h157, h159, h178, hc23, hlam, hphi, u2ehi4]
                  · linarith only [h156, h158, h159, hlam, hphi, ht23, u2ehi3, u3elo4]
                · linarith only [h155, h158, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h155, h157, hc25, hlam, hphi, u2ehi2]
            · linarith only [h155, h156, hc24, hlam, hphi, u2ehi2]
          · linarith only [h155, hlam, hphi, ht23, u2ehi0, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h231 | h231
          · rcases m.htr 0 2 4 (by decide) (by decide) with h232 | h232
            · rcases m.htr 0 2 5 (by decide) (by decide) with h233 | h233
              · rcases m.htr 0 3 4 (by decide) (by decide) with h234 | h234
                · rcases m.htr 0 3 5 (by decide) (by decide) with h235 | h235
                  · linarith only [h152, h154, h235, hlam]
                  · linarith only [h231, h235, hlam, hphi, ht23, u2ehi2, u3elo4]
                · linarith only [h231, h234, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h231, h233, hc25, hlam, hphi, u2ehi2]
            · linarith only [h231, h232, hc24, hlam, hphi, u2ehi2]
          · linarith only [h231, hlam, hphi, ht23, u2ehi0, u3elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h242 | h242
        · rcases m.htr 0 2 3 (by decide) (by decide) with h243 | h243
          · rcases m.htr 0 2 4 (by decide) (by decide) with h244 | h244
            · rcases m.htr 0 2 5 (by decide) (by decide) with h245 | h245
              · rcases m.htr 0 3 4 (by decide) (by decide) with h246 | h246
                · linarith only [h152, h153, h246, hlam]
                · linarith only [h243, h246, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h243, h245, hc25, hlam, hphi, u2ehi2]
            · linarith only [h243, h244, hc24, hlam, hphi, u2ehi2]
          · linarith only [h243, hlam, hphi, ht23, u2ehi0, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h252 | h252
          · rcases m.htr 0 2 4 (by decide) (by decide) with h253 | h253
            · rcases m.htr 0 2 5 (by decide) (by decide) with h254 | h254
              · rcases m.htr 0 3 4 (by decide) (by decide) with h255 | h255
                · linarith only [h152, h153, h255, hlam]
                · linarith only [h252, h255, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h252, h254, hc25, hlam, hphi, u2ehi2]
            · linarith only [h252, h253, hc24, hlam, hphi, u2ehi2]
          · linarith only [h252, hlam, hphi, ht23, u2ehi0, u3elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h261 | h261
      · rcases m.htr 0 1 5 (by decide) (by decide) with h262 | h262
        · rcases m.htr 0 2 3 (by decide) (by decide) with h263 | h263
          · rcases m.htr 0 2 4 (by decide) (by decide) with h264 | h264
            · linarith only [h152, h261, h264, hlam, hphi, ht23, u2ehi3, u3elo1]
            · linarith only [h263, h264, hc24, hlam, hphi, u2ehi2]
          · linarith only [h263, hlam, hphi, ht23, u2ehi0, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h268 | h268
          · rcases m.htr 0 2 4 (by decide) (by decide) with h269 | h269
            · linarith only [h152, h261, h269, hlam, hphi, ht23, u2ehi3, u3elo1]
            · linarith only [h268, h269, hc24, hlam, hphi, u2ehi2]
          · linarith only [h268, hlam, hphi, ht23, u2ehi0, u3elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h273 | h273
        · rcases m.htr 0 2 3 (by decide) (by decide) with h274 | h274
          · rcases m.htr 0 2 4 (by decide) (by decide) with h275 | h275
            · rcases m.htr 0 2 5 (by decide) (by decide) with h276 | h276
              · linarith only [h152, h273, h276, hlam, hphi, ht23, u2ehi4, u3elo1]
              · linarith only [h274, h276, hc25, hlam, hphi, u2ehi2]
            · linarith only [h274, h275, hc24, hlam, hphi, u2ehi2]
          · linarith only [h274, hlam, hphi, ht23, u2ehi0, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h281 | h281
          · rcases m.htr 0 2 4 (by decide) (by decide) with h282 | h282
            · rcases m.htr 0 2 5 (by decide) (by decide) with h283 | h283
              · rcases m.htr 0 3 4 (by decide) (by decide) with h284 | h284
                · rcases m.htr 0 3 5 (by decide) (by decide) with h285 | h285
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h286 | h286
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h288 | h288
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h289 | h289
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h290 | h290
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h291 | h291
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h292 | h292
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h293 | h293
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h294 | h294
                                    · rcases h0bigk with h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [hlam, p295_0]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [h0, hlam, p295_1]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [h152, hlam, p295_0]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [h261, hlam, p295_1]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [h273, hlam, p295_1]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        rcases p295_3 (m.d 0 1) (by simp) with h301 | h301
                                        · linarith only [h0, h301, hlam]
                                        · rcases p295_3 (m.d 0 2) (by simp) with h303 | h303
                                          · rcases p295_3 (m.d 0 3) (by simp) with h304 | h304
                                            · linarith only [h281, h304, hlam]
                                            · linarith only [h152, h304, hlam]
                                          · linarith only [h0, h303, hlam]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [hlam, p295_0]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [h0, h281, h291, h294, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p295_1]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        rcases p295_3 (m.d 0 1) (by simp) with h310 | h310
                                        · linarith only [h0, h310, hlam]
                                        · rcases p295_3 (m.d 0 2) (by simp) with h312 | h312
                                          · rcases p295_3 (m.d 0 3) (by simp) with h313 | h313
                                            · linarith only [h281, h313, hlam]
                                            · linarith only [h284, h313, hlam]
                                          · linarith only [h282, h312, hlam]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        rcases p295_3 (m.d 0 1) (by simp) with h317 | h317
                                        · linarith only [h0, h317, hlam]
                                        · rcases p295_3 (m.d 0 2) (by simp) with h319 | h319
                                          · rcases p295_3 (m.d 0 3) (by simp) with h320 | h320
                                            · linarith only [h281, h320, hlam]
                                            · linarith only [h285, h320, hlam]
                                          · linarith only [h283, h319, hlam]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, p295_1, u3elo0]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [h281, hlam, p295_1]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [hlam, p295_0]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [h152, h283, h286, hlam, hphi, ht23, p295_1, u2ehi4, u3elo1]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [h152, h283, hlam, hphi, ht23, p295_1, u2ehi4, u3elo1]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [h261, h290, hc01, hlam, hphi, ht12, ht23, p295_1, u3elo1]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [h282, hlam, p295_0]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [h284, hlam, p295_0]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [hlam, p295_0]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [h261, h283, h290, hlam, hphi, ht23, p295_1, u2ehi4, u3elo1]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [h152, h285, hc01, hlam, hphi, ht12, ht23, p295_1, u3elo1]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [h283, hlam, p295_1]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [h285, hlam, p295_0]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [h286, hlam, p295_1]
                                      · have p295_0 := h295c.1
                                        have p295_1 := h295c.2.1
                                        have p295_2 := h295c.2.2.1
                                        have p295_3 := h295c.2.2.2
                                        linarith only [hlam, p295_0]
                                    · rcases h0bigk with h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [hlam, p339_0]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [h0, hlam, p339_1]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [h152, hlam, p339_0]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [h261, hlam, p339_1]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [h273, hlam, p339_1]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        rcases p339_3 (m.d 0 1) (by simp) with h345 | h345
                                        · linarith only [h0, h345, hlam]
                                        · rcases p339_3 (m.d 0 2) (by simp) with h347 | h347
                                          · rcases p339_3 (m.d 0 3) (by simp) with h348 | h348
                                            · linarith only [h281, h348, hlam]
                                            · linarith only [h152, h348, hlam]
                                          · linarith only [h0, h347, hlam]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [hlam, p339_0]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [h0, h281, h291, h293, h294, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p339_1]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [h0, h282, h293, h294, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p339_1]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        rcases p339_3 (m.d 0 1) (by simp) with h355 | h355
                                        · linarith only [h0, h355, hlam]
                                        · rcases p339_3 (m.d 0 2) (by simp) with h357 | h357
                                          · rcases p339_3 (m.d 0 3) (by simp) with h358 | h358
                                            · linarith only [h281, h358, hlam]
                                            · linarith only [h285, h358, hlam]
                                          · linarith only [h283, h357, hlam]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, p339_1, u3elo0]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [h281, hlam, p339_1]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [hlam, p339_0]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [h152, h282, h293, h294, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p339_1, u3elo1]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [h152, h283, hlam, hphi, ht23, p339_1, u2ehi4, u3elo1]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [h261, h290, hc01, hlam, hphi, ht12, ht23, p339_1, u3elo1]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [h282, hlam, p339_0]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [h284, hlam, p339_0]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [hlam, p339_0]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [h261, h283, h290, hlam, hphi, ht23, p339_1, u2ehi4, u3elo1]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [h152, h285, hc01, hlam, hphi, ht12, ht23, p339_1, u3elo1]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [h283, hlam, p339_1]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [h285, hlam, p339_0]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [h286, hlam, p339_1]
                                      · have p339_0 := h339c.1
                                        have p339_1 := h339c.2.1
                                        have p339_2 := h339c.2.2.1
                                        have p339_3 := h339c.2.2.2
                                        linarith only [hlam, p339_0]
                                  · linarith only [h261, h286, h290, h293, hlam, hphi, ht23, u2ehi3, u3elo1]
                                · linarith only [h292, hlam, hphi, ht23, u2ehi2, u3elo4]
                              · linarith only [h291, hlam, hphi, ht23, u2ehi2, u3elo3]
                            · linarith only [h152, h284, h290, hlam]
                          · linarith only [h0, h281, h289, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h0, h281, h288, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h0, h281, h287, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h384 | h384
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h385 | h385
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h386 | h386
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h387 | h387
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h388 | h388
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h389 | h389
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h390 | h390
                                  · linarith only [h0, h261, h281, h286, h388, h390, hc01, hc12, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h392 | h392
                                    · linarith only [h152, h281, h282, h286, h388, h392, hlam, hphi, ht23, u2ehi3, u3elo1]
                                    · rcases h0bigk with h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h0, hlam, p394_1]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h152, hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h261, hlam, p394_1]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h273, hlam, p394_1]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        rcases p394_3 (m.d 0 1) (by simp) with h400 | h400
                                        · linarith only [h0, h400, hlam]
                                        · rcases p394_3 (m.d 0 2) (by simp) with h402 | h402
                                          · rcases p394_3 (m.d 0 3) (by simp) with h403 | h403
                                            · linarith only [h281, h403, hlam]
                                            · linarith only [h152, h403, hlam]
                                          · linarith only [h0, h402, hlam]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        rcases p394_3 (m.d 0 1) (by simp) with h408 | h408
                                        · linarith only [h0, h408, hlam]
                                        · rcases p394_3 (m.d 0 2) (by simp) with h410 | h410
                                          · rcases p394_3 (m.d 0 3) (by simp) with h411 | h411
                                            · linarith only [h281, h411, hlam]
                                            · rcases p394_3 (m.d 0 4) (by simp) with h413 | h413
                                              · linarith only [h282, h413, hlam]
                                              · rcases p394_3 (m.d 0 5) (by simp) with h415 | h415
                                                · linarith only [h283, h415, hlam]
                                                · rcases h3bigk with h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [hlam, p417_0]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [h152, hlam, p417_1]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [h0, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p394_1, p417_1]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p394_1, p417_1]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [h0, h392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p394_1, p417_1]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [hc03, hlam, hphi, p417_1, u3elo1]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [hlam, p417_0]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [h389, hlam, hphi, ht23, p417_1, u2ehi4, u3elo1]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    rcases p417_3 (m.d 0 3) (by simp) with h426 | h426
                                                    · linarith only [h152, h426, hlam]
                                                    · linarith only [h284, h426, hlam]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    rcases p417_3 (m.d 0 3) (by simp) with h429 | h429
                                                    · linarith only [h152, h429, hlam]
                                                    · linarith only [h285, h429, hlam]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [h281, hlam, p417_0]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [h384, hlam, p417_0]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [hlam, p417_0]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [h0, h281, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p394_1, p417_1]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [h0, h281, h392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p394_1, p417_1]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [h284, hlam, p417_0]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [h387, hlam, p417_0]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [h388, hlam, p417_0]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [hlam, p417_0]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [h392, hlam, p417_1]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [h285, hlam, p417_0]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [h261, h387, hc01, hlam, hphi, ht12, ht23, p417_1, u3elo4]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [h389, hlam, p417_0]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [h0, h282, h285, h286, h389, hc12, hc34, hlam, hphi, ht01, ht0b, ht23, ht45, ht5b, p394_1, p417_1, u2ehi3, u3elo2]
                                                  · have p417_0 := h417c.1
                                                    have p417_1 := h417c.2.1
                                                    have p417_2 := h417c.2.2.1
                                                    have p417_3 := h417c.2.2.2
                                                    linarith only [hlam, p417_0]
                                          · linarith only [h281, h410, hlam]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        rcases p394_3 (m.d 0 1) (by simp) with h448 | h448
                                        · linarith only [h0, h448, hlam]
                                        · rcases p394_3 (m.d 0 2) (by simp) with h450 | h450
                                          · rcases p394_3 (m.d 0 3) (by simp) with h451 | h451
                                            · linarith only [h281, h451, hlam]
                                            · linarith only [h284, h451, hlam]
                                          · linarith only [h282, h450, hlam]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        rcases p394_3 (m.d 0 1) (by simp) with h455 | h455
                                        · linarith only [h0, h455, hlam]
                                        · rcases p394_3 (m.d 0 2) (by simp) with h457 | h457
                                          · rcases p394_3 (m.d 0 3) (by simp) with h458 | h458
                                            · linarith only [h281, h458, hlam]
                                            · linarith only [h285, h458, hlam]
                                          · linarith only [h283, h457, hlam]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, p394_1, u3elo0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h281, hlam, p394_1]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h152, h261, hc01, hlam, hphi, ht12, ht23, p394_1, u3elo1]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h152, h283, h390, hlam, hphi, ht23, p394_1, u2ehi3, u3elo1]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h152, h284, hc01, hlam, hphi, ht12, ht23, p394_1, u3elo1]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h282, hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h284, hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h286, hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h152, h285, hc01, hlam, hphi, ht12, ht23, p394_1, u3elo1]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h283, hlam, p394_1]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h285, hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h152, h261, h285, hc01, hlam, hphi, ht12, ht23, p394_1, u3elo1]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [hlam, p394_0]
                                · linarith only [h389, hlam, hphi, ht23, u2ehi2, u3elo4]
                              · linarith only [h388, hlam, hphi, ht23, u2ehi2, u3elo3]
                            · linarith only [h152, h284, h387, hlam]
                          · linarith only [h0, h281, h386, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h0, h281, h385, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h0, h384, hlam, hphi, ht23, u2ehi0, u3elo2]
                  · linarith only [h281, h285, hlam, hphi, ht23, u2ehi2, u3elo4]
                · linarith only [h281, h284, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h282, h283, hc25, hlam, hphi, u2ehi3]
            · linarith only [h281, h282, hc24, hlam, hphi, u2ehi2]
          · linarith only [h281, hlam, hphi, ht23, u2ehi0, u3elo2]

end R2N4
