import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_13_25_L_I_L_0_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h1bigk := hb1.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · linarith only [h1, h11, h8, hc23, hlam, hphi, u3elo0]
                      · linarith only [h1, h10, h7, hc23, hlam, hphi, u3elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                        · linarith only [h0, h16, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · linarith only [h1, h16, h8, hc23, hlam, hphi, u3elo0]
                      · linarith only [h1, h15, h7, hc23, hlam, hphi, u3elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                    · linarith only [h20, h7, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                        · linarith only [h23, h8, hc13, hlam, hphi, u3elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                          · linarith only [h0, h20, h25, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                            · linarith only [h20, h22, h27, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · rcases h1bigk with h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [hlam, p29_0]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [h6, hc01, hlam, hphi, ht0b, ht5b, p29_1, u5ehi2]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                rcases p29_3 (m.d 0 1) (by simp) with h32 | h32
                                · rcases p29_3 (m.d 1 2) (by simp) with h33 | h33
                                  · linarith only [h0, h33, hlam]
                                  · linarith only [h33, h4, hlam]
                                · linarith only [h32, hlam, p29_0]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                rcases p29_3 (m.d 0 1) (by simp) with h37 | h37
                                · rcases p29_3 (m.d 1 2) (by simp) with h38 | h38
                                  · linarith only [h0, h38, hlam]
                                  · linarith only [h38, h5, hlam]
                                · linarith only [h37, hlam, p29_0]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                rcases p29_3 (m.d 0 1) (by simp) with h42 | h42
                                · rcases p29_3 (m.d 1 2) (by simp) with h43 | h43
                                  · linarith only [h0, h43, hlam]
                                  · linarith only [h43, h6, hlam]
                                · linarith only [h42, hlam, p29_0]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [h0, hlam, p29_0]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [hlam, p29_0]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [h0, h22, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p29_1]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                rcases p29_3 (m.d 0 1) (by simp) with h50 | h50
                                · rcases p29_3 (m.d 1 2) (by simp) with h51 | h51
                                  · rcases p29_3 (m.d 1 3) (by simp) with h52 | h52
                                    · linarith only [h4, h52, hlam]
                                    · linarith only [h52, h7, hlam]
                                  · linarith only [h5, h51, hlam]
                                · linarith only [h2, h50, hlam]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [h0, h22, h23, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p29_1]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [h1, hlam, p29_0]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [h4, hlam, p29_1]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [hlam, p29_0]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [h22, h5, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p29_1, u3elo4]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [h8, hlam, p29_1]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [h2, hlam, p29_0]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [h5, hlam, p29_1]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [h7, hlam, p29_0]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [hlam, p29_0]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [h20, hlam, p29_1]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [h3, hlam, p29_0]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [h6, hlam, p29_1]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [h22, h3, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p29_1]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                rcases p29_3 (m.d 0 1) (by simp) with h71 | h71
                                · rcases p29_3 (m.d 1 2) (by simp) with h72 | h72
                                  · rcases p29_3 (m.d 1 3) (by simp) with h73 | h73
                                    · linarith only [h73, h8, hlam]
                                    · linarith only [h7, h73, hlam]
                                  · linarith only [h5, h72, hlam]
                                · linarith only [h2, h71, hlam]
                              · have p29_0 := h29c.1
                                have p29_1 := h29c.2.1
                                have p29_2 := h29c.2.2.1
                                have p29_3 := h29c.2.2.2
                                linarith only [hlam, p29_0]
                      · linarith only [h22, h7, hc23, hlam, hphi, u3elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h80 | h80
                  · linarith only [h7, h80, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                      · linarith only [h7, h83, hc13, hlam, hphi, u3elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h85 | h85
                        · linarith only [h4, h80, h85, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
                          · linarith only [h0, h5, h87, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · linarith only [h7, h82, h83, h87, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h90 | h90
                      · linarith only [h7, h90, hc13, hlam, hphi, u3elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                        · linarith only [h4, h7, h80, h92, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h94 | h94
                          · linarith only [h5, h82, h94, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h96 | h96
                            · linarith only [h7, h82, h96, hc13, hlam, hphi, u3elo3]
                            · rcases h1bigk with h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h6, hc01, hlam, hphi, ht0b, ht5b, p98_1, u5ehi2]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                rcases p98_3 (m.d 0 1) (by simp) with h101 | h101
                                · rcases p98_3 (m.d 1 2) (by simp) with h102 | h102
                                  · linarith only [h0, h102, hlam]
                                  · linarith only [h102, h4, hlam]
                                · linarith only [h101, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                rcases p98_3 (m.d 0 1) (by simp) with h106 | h106
                                · rcases p98_3 (m.d 1 2) (by simp) with h107 | h107
                                  · linarith only [h0, h107, hlam]
                                  · linarith only [h107, h5, hlam]
                                · linarith only [h106, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                rcases p98_3 (m.d 0 1) (by simp) with h111 | h111
                                · rcases p98_3 (m.d 1 2) (by simp) with h112 | h112
                                  · linarith only [h0, h112, hlam]
                                  · linarith only [h112, h6, hlam]
                                · linarith only [h111, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h0, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                rcases p98_3 (m.d 0 1) (by simp) with h118 | h118
                                · rcases p98_3 (m.d 1 2) (by simp) with h119 | h119
                                  · rcases p98_3 (m.d 1 3) (by simp) with h120 | h120
                                    · linarith only [h120, h4, hlam]
                                    · rcases p98_3 (m.d 1 4) (by simp) with h122 | h122
                                      · linarith only [h122, h5, hlam]
                                      · linarith only [h122, h7, hlam]
                                  · linarith only [h119, h4, hlam]
                                · linarith only [h1, h118, hlam]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                rcases p98_3 (m.d 0 1) (by simp) with h127 | h127
                                · rcases p98_3 (m.d 1 2) (by simp) with h128 | h128
                                  · rcases p98_3 (m.d 1 3) (by simp) with h129 | h129
                                    · linarith only [h129, h4, hlam]
                                    · rcases p98_3 (m.d 1 4) (by simp) with h131 | h131
                                      · linarith only [h131, h5, hlam]
                                      · rcases p98_3 (m.d 1 5) (by simp) with h133 | h133
                                        · linarith only [h133, h6, hlam]
                                        · linarith only [h133, h82, hlam]
                                  · linarith only [h128, h5, hlam]
                                · linarith only [h127, h2, hlam]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht5b, p98_1, u5ehi2]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h1, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h4, hlam, p98_1]
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
                                linarith only [h80, hlam, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h2, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h5, hlam, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h4, h7, hc23, hlam, hphi, p98_1, u3elo3]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h82, hlam, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h3, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h6, hlam, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h4, h80, hc23, hlam, hphi, p98_1, u3elo4]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h4, h7, h80, hc23, hlam, hphi, p98_1, u3elo4]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h154 | h154
                · rcases m.htr 1 3 5 (by decide) (by decide) with h155 | h155
                  · linarith only [h155, h4, h6, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h157 | h157
                    · linarith only [h154, h155, h157, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h160 | h160
                        · linarith only [h155, h160, hc13, hlam, hphi, u3elo2]
                        · linarith only [h159, h160, h4, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h154, h159, hc23, hlam, hphi, u3elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h164 | h164
                  · linarith only [h154, h164, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h166 | h166
                    · linarith only [h166, h5, h6, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h168 | h168
                      · linarith only [h154, h168, hc13, hlam, hphi, u3elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h170 | h170
                        · linarith only [h164, h170, h4, h6, hlam]
                        · linarith only [h168, h170, h5, h6, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h173 | h173
              · rcases m.htr 1 3 4 (by decide) (by decide) with h174 | h174
                · linarith only [h174, h4, h5, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h176 | h176
                  · linarith only [h174, h176, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h178 | h178
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h179 | h179
                      · linarith only [h174, h179, hc13, hlam, hphi, u3elo2]
                      · linarith only [h173, h179, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi2]
                    · linarith only [h173, h178, h5, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h183 | h183
                · linarith only [h183, h4, h5, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h185 | h185
                  · linarith only [h183, h185, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h187 | h187
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h188 | h188
                      · linarith only [h183, h188, h4, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · linarith only [h188, h4, h5, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h191 | h191
                      · linarith only [h187, h191, h4, h5, hc34, hc45, hlam, hphi]
                      · linarith only [h191, h4, h5, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h194 | h194
            · rcases m.htr 1 2 5 (by decide) (by decide) with h195 | h195
              · linarith only [h195, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h197 | h197
                · rcases m.htr 1 3 5 (by decide) (by decide) with h198 | h198
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h199 | h199
                    · linarith only [h194, h199, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h201 | h201
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h202 | h202
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h203 | h203
                          · linarith only [h194, h195, h199, h202, h203, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h205 | h205
                            · linarith only [h195, h203, h205, hc12, hlam, hphi, ht23, u3elo3]
                            · rcases h1bigk with h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                rcases p207_3 (m.d 0 1) (by simp) with h209 | h209
                                · rcases p207_3 (m.d 1 2) (by simp) with h210 | h210
                                  · linarith only [h210, hlam, p207_0]
                                  · rcases p207_3 (m.d 1 3) (by simp) with h212 | h212
                                    · linarith only [h1, h212, hlam]
                                    · linarith only [h212, h4, hlam]
                                · linarith only [h209, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h198, hc01, hlam, hphi, ht0b, ht5b, p207_1, u5ehi3]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                rcases p207_3 (m.d 0 1) (by simp) with h217 | h217
                                · rcases p207_3 (m.d 1 2) (by simp) with h218 | h218
                                  · linarith only [h0, h218, hlam]
                                  · linarith only [h194, h218, hlam]
                                · linarith only [h217, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                rcases p207_3 (m.d 0 1) (by simp) with h222 | h222
                                · rcases p207_3 (m.d 1 2) (by simp) with h223 | h223
                                  · linarith only [h0, h223, hlam]
                                  · rcases p207_3 (m.d 1 3) (by simp) with h225 | h225
                                    · linarith only [h1, h225, hlam]
                                    · linarith only [h198, h225, hlam]
                                · linarith only [h222, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h0, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h4, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h195, h203, hc14, hc45, hlam, hphi, p207_1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h195, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h1, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, p207_1, u3elo1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                rcases p207_3 (m.d 0 1) (by simp) with h237 | h237
                                · rcases p207_3 (m.d 1 2) (by simp) with h238 | h238
                                  · linarith only [h238, h4, hlam]
                                  · linarith only [h194, h238, hlam]
                                · linarith only [h2, h237, hlam]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p207_1, u3elo0, u5ehi1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h2, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h194, hlam, p207_1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h197, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h199, hlam, p207_1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h3, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h194, h201, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p207_1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h198, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                rcases p207_3 (m.d 0 1) (by simp) with h251 | h251
                                · rcases p207_3 (m.d 1 2) (by simp) with h252 | h252
                                  · linarith only [h195, h252, hlam]
                                  · linarith only [h194, h252, hlam]
                                · linarith only [h2, h251, hlam]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                        · linarith only [h194, h201, h202, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h198, h201, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h259 | h259
                    · linarith only [h194, h198, h259, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h261 | h261
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h262 | h262
                        · linarith only [h194, h198, h261, h262, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · linarith only [h194, h261, h262, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h194, h261, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · linarith only [h194, h197, h4, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h267 | h267
              · linarith only [h267, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h269 | h269
                · rcases m.htr 1 3 5 (by decide) (by decide) with h270 | h270
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h271 | h271
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h272 | h272
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h273 | h273
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h274 | h274
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h275 | h275
                            · linarith only [h269, h275, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                            · rcases h1bigk with h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                rcases p277_3 (m.d 0 1) (by simp) with h279 | h279
                                · rcases p277_3 (m.d 1 2) (by simp) with h280 | h280
                                  · linarith only [h280, hlam, p277_0]
                                  · rcases p277_3 (m.d 1 3) (by simp) with h282 | h282
                                    · linarith only [h1, h282, hlam]
                                    · linarith only [h282, h4, hlam]
                                · linarith only [h279, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h269, h271, h275, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p277_1]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h271, h275, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p277_1]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                rcases p277_3 (m.d 0 1) (by simp) with h288 | h288
                                · rcases p277_3 (m.d 1 2) (by simp) with h289 | h289
                                  · linarith only [h0, h289, hlam]
                                  · rcases p277_3 (m.d 1 3) (by simp) with h291 | h291
                                    · linarith only [h1, h291, hlam]
                                    · linarith only [h270, h291, hlam]
                                · linarith only [h288, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h0, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h4, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h194, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h267, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h1, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h1, hc12, hlam, hphi, ht23, p277_1, u3elo0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h1, h271, h275, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p277_1, u3elo0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p277_1, u3elo0, u5ehi1]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h2, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h194, h272, hc12, hlam, hphi, ht23, p277_1, u3elo2]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h269, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h194, h270, h272, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p277_1, u3elo2, u5ehi3]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h3, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h267, h272, h274, hc12, hlam, hphi, ht23, p277_1, u3elo2]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h270, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h271, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [hlam, p277_0]
                          · linarith only [h194, h271, h274, hlam]
                        · linarith only [h194, h271, h272, h273, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                      · linarith only [h270, h272, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h318 | h318
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h319 | h319
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h320 | h320
                          · linarith only [h194, h271, h318, h320, hc12, hlam, hphi, ht23, u3elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h322 | h322
                            · linarith only [h194, h320, h322, hc12, hlam, hphi, ht23, u3elo3]
                            · rcases h1bigk with h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                rcases p324_3 (m.d 0 1) (by simp) with h326 | h326
                                · rcases p324_3 (m.d 1 2) (by simp) with h327 | h327
                                  · linarith only [h327, hlam, p324_0]
                                  · rcases p324_3 (m.d 1 3) (by simp) with h329 | h329
                                    · linarith only [h1, h329, hlam]
                                    · linarith only [h329, h4, hlam]
                                · linarith only [h326, hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h270, hc01, hlam, hphi, ht0b, ht5b, p324_1, u5ehi3]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                rcases p324_3 (m.d 0 1) (by simp) with h334 | h334
                                · rcases p324_3 (m.d 1 2) (by simp) with h335 | h335
                                  · linarith only [h0, h335, hlam]
                                  · rcases p324_3 (m.d 1 3) (by simp) with h337 | h337
                                    · linarith only [h1, h337, hlam]
                                    · linarith only [h269, h337, hlam]
                                · linarith only [h334, hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                rcases p324_3 (m.d 0 1) (by simp) with h341 | h341
                                · rcases p324_3 (m.d 1 2) (by simp) with h342 | h342
                                  · linarith only [h0, h342, hlam]
                                  · rcases p324_3 (m.d 1 3) (by simp) with h344 | h344
                                    · linarith only [h1, h344, hlam]
                                    · linarith only [h270, h344, hlam]
                                · linarith only [h341, hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h0, hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h4, hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h194, hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h267, hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h1, hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, p324_1, u3elo1]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h1, h194, hc12, hlam, hphi, ht23, p324_1, u3elo0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p324_1, u3elo0, u5ehi1]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h2, hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h194, h320, hc12, hc45, hlam, hphi, ht23, ht34, p324_1]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h269, hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h271, hlam, p324_1]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h3, hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h267, h319, hc12, hlam, hphi, ht23, p324_1, u3elo2]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h270, hlam, p324_0]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [h194, h267, h319, hc12, hlam, hphi, ht23, p324_1, u3elo2]
                              · have p324_0 := h324c.1
                                have p324_1 := h324c.2.1
                                have p324_2 := h324c.2.2.1
                                have p324_3 := h324c.2.2.2
                                linarith only [hlam, p324_0]
                        · linarith only [h319, h4, hc12, hlam, hphi, ht23, u3elo4]
                      · linarith only [h270, h318, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h370 | h370
                    · linarith only [h269, h270, h370, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h372 | h372
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h373 | h373
                        · linarith only [h270, h373, hc13, hlam, hphi, u3elo2]
                        · linarith only [h373, h4, hc12, hlam, hphi, ht23, u3elo4]
                      · linarith only [h372, h4, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h377 | h377
                  · linarith only [h269, h377, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h379 | h379
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h380 | h380
                      · linarith only [h269, h380, hc13, hlam, hphi, u3elo2]
                      · linarith only [h380, h4, hc12, hlam, hphi, ht23, u3elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h383 | h383
                      · linarith only [h269, h383, h4, hc12, hlam, hphi, ht23, u3elo2]
                      · linarith only [h383, h4, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h386 | h386
          · rcases m.htr 1 2 4 (by decide) (by decide) with h387 | h387
            · rcases m.htr 1 2 5 (by decide) (by decide) with h388 | h388
              · linarith only [h0, h3, h388, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h390 | h390
                · rcases m.htr 1 3 5 (by decide) (by decide) with h391 | h391
                  · linarith only [h1, h3, h388, h391, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h3, h386, h391, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h394 | h394
                  · linarith only [h0, h3, h387, h388, h390, h394, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h3, h386, h394, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h397 | h397
              · linarith only [h2, h3, h387, h397, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h399 | h399
                · linarith only [h386, h387, h399, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h401 | h401
                  · linarith only [h399, h401, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · linarith only [h2, h3, h386, h387, h401, hc23, hlam, hphi, u3elo4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h404 | h404
            · rcases m.htr 1 2 5 (by decide) (by decide) with h405 | h405
              · linarith only [h0, h3, h405, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h407 | h407
                · rcases m.htr 1 3 5 (by decide) (by decide) with h408 | h408
                  · linarith only [h1, h3, h405, h408, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h1, h3, h386, h408, hc12, hlam, hphi, ht23, u3elo4]
                · linarith only [h386, h404, h407, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h412 | h412
              · linarith only [h1, h3, h386, h412, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h414 | h414
                · rcases m.htr 1 3 5 (by decide) (by decide) with h415 | h415
                  · linarith only [h1, h3, h412, h415, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h1, h3, h404, h414, h415, hc12, hlam, hphi, ht23, u3elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h418 | h418
                  · linarith only [h414, h418, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · linarith only [h2, h3, h414, h418, hc13, hlam, hphi, u3elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h421 | h421
        · rcases m.htr 1 2 3 (by decide) (by decide) with h422 | h422
          · rcases m.htr 1 2 4 (by decide) (by decide) with h423 | h423
            · linarith only [h0, h2, h423, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h425 | h425
              · linarith only [h0, h2, h423, h425, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h427 | h427
                · linarith only [h2, h421, h422, h425, h427, hc23, hlam, hphi, u3elo1]
                · linarith only [h2, h421, h422, h425, h427, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h430 | h430
            · linarith only [h1, h2, h421, h422, h430, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h432 | h432
              · linarith only [h1, h2, h422, h432, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h434 | h434
                · linarith only [h1, h2, h434, hlam]
                · linarith only [h1, h2, h422, h434, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h437 | h437
          · rcases m.htr 1 2 4 (by decide) (by decide) with h438 | h438
            · linarith only [h0, h2, h438, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h440 | h440
              · linarith only [h0, h2, h440, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h442 | h442
                · linarith only [h0, h2, h437, h442, hlam]
                · linarith only [h0, h2, h442, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h445 | h445
            · linarith only [h1, h2, h437, h445, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h447 | h447
              · linarith only [h1, h2, h437, h447, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h449 | h449
                · linarith only [h1, h2, h449, hlam]
                · linarith only [h1, h2, h437, h449, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h453 | h453
    · rcases m.htr 0 1 4 (by decide) (by decide) with h454 | h454
      · rcases m.htr 0 1 5 (by decide) (by decide) with h455 | h455
        · rcases m.htr 1 2 3 (by decide) (by decide) with h456 | h456
          · rcases m.htr 1 2 4 (by decide) (by decide) with h457 | h457
            · rcases m.htr 1 2 5 (by decide) (by decide) with h458 | h458
              · rcases m.htr 1 3 4 (by decide) (by decide) with h459 | h459
                · rcases m.htr 1 3 5 (by decide) (by decide) with h460 | h460
                  · linarith only [h0, h453, h460, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h462 | h462
                    · linarith only [h459, h460, h462, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h464 | h464
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h465 | h465
                        · linarith only [h460, h465, hc13, hlam, hphi, u3elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h467 | h467
                          · linarith only [h456, h460, h462, h464, h467, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h469 | h469
                            · linarith only [h0, h454, h457, h462, h464, h469, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                            · rcases h1bigk with h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h0, hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h0, h456, h464, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                rcases p471_3 (m.d 0 1) (by simp) with h475 | h475
                                · rcases p471_3 (m.d 1 2) (by simp) with h476 | h476
                                  · rcases p471_3 (m.d 1 3) (by simp) with h477 | h477
                                    · linarith only [h453, h477, hlam]
                                    · linarith only [h459, h477, hlam]
                                  · linarith only [h457, h476, hlam]
                                · linarith only [h475, hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h0, h456, h460, h464, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h453, h456, h464, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                rcases p471_3 (m.d 0 1) (by simp) with h485 | h485
                                · linarith only [h0, h485, hlam]
                                · linarith only [h453, h485, hlam]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                rcases p471_3 (m.d 0 1) (by simp) with h488 | h488
                                · linarith only [h0, h488, hlam]
                                · linarith only [h454, h488, hlam]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                rcases p471_3 (m.d 0 1) (by simp) with h491 | h491
                                · linarith only [h0, h491, hlam]
                                · linarith only [h455, h491, hlam]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h453, hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h456, hlam, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h0, h455, h460, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h460, hlam, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h454, hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h457, hlam, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h459, hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h462, hlam, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h455, hlam, p471_0]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h458, hlam, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h0, h455, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [h0, h455, h457, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p471_1]
                              · have p471_0 := h471c.1
                                have p471_1 := h471c.2.1
                                have p471_2 := h471c.2.2.1
                                have p471_3 := h471c.2.2.2
                                linarith only [hlam, p471_0]
                      · linarith only [h459, h460, h464, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h510 | h510
                  · linarith only [h459, h510, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h512 | h512
                    · linarith only [h0, h454, h512, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h514 | h514
                      · linarith only [h459, h514, hc13, hlam, hphi, u3elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h516 | h516
                        · linarith only [h456, h510, h516, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h518 | h518
                          · linarith only [h457, h512, h518, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h520 | h520
                            · linarith only [h459, h512, h520, hc13, hlam, hphi, u3elo3]
                            · rcases h1bigk with h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [hlam, p522_0]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [h0, hlam, p522_0]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                rcases p522_3 (m.d 0 1) (by simp) with h525 | h525
                                · rcases p522_3 (m.d 1 2) (by simp) with h526 | h526
                                  · rcases p522_3 (m.d 1 3) (by simp) with h527 | h527
                                    · linarith only [h527, hlam, p522_0]
                                    · rcases p522_3 (m.d 1 4) (by simp) with h529 | h529
                                      · linarith only [h454, h529, hlam]
                                      · linarith only [h459, h529, hlam]
                                  · linarith only [h456, h526, hlam]
                                · linarith only [h525, hlam, p522_0]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                rcases p522_3 (m.d 0 1) (by simp) with h534 | h534
                                · rcases p522_3 (m.d 1 2) (by simp) with h535 | h535
                                  · rcases p522_3 (m.d 1 3) (by simp) with h536 | h536
                                    · linarith only [h453, h536, hlam]
                                    · rcases p522_3 (m.d 1 4) (by simp) with h538 | h538
                                      · linarith only [h538, hlam, p522_0]
                                      · rcases p522_3 (m.d 1 5) (by simp) with h540 | h540
                                        · linarith only [h455, h540, hlam]
                                        · linarith only [h512, h540, hlam]
                                  · linarith only [h457, h535, hlam]
                                · linarith only [h534, hlam, p522_0]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p522_1, u5ehi1]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [h455, hc12, hlam, hphi, ht01, ht0b, ht5b, p522_1, u5ehi1]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [hlam, p522_0]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                rcases p522_3 (m.d 0 1) (by simp) with h548 | h548
                                · linarith only [h0, h548, hlam]
                                · linarith only [h453, h548, hlam]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                rcases p522_3 (m.d 0 1) (by simp) with h551 | h551
                                · linarith only [h0, h551, hlam]
                                · linarith only [h454, h551, hlam]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                rcases p522_3 (m.d 0 1) (by simp) with h554 | h554
                                · linarith only [h0, h554, hlam]
                                · linarith only [h455, h554, hlam]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [h453, hlam, p522_0]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [h456, hlam, p522_1]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [hlam, p522_0]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [h459, hlam, p522_1]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [h510, hlam, p522_1]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [h454, hlam, p522_0]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [h457, hlam, p522_1]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [h0, h454, h456, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p522_1]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [hlam, p522_0]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [h512, hlam, p522_1]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [h455, hlam, p522_0]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [h458, hlam, p522_1]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [h0, h455, h456, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p522_1]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [h0, h455, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p522_1]
                              · have p522_0 := h522c.1
                                have p522_1 := h522c.2.1
                                have p522_2 := h522c.2.2.1
                                have p522_3 := h522c.2.2.2
                                linarith only [hlam, p522_0]
              · linarith only [h0, h455, h458, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h0, h455, h457, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
          · linarith only [h0, h455, h456, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h575 | h575
          · rcases m.htr 1 2 4 (by decide) (by decide) with h576 | h576
            · rcases m.htr 1 2 5 (by decide) (by decide) with h577 | h577
              · rcases m.htr 1 3 4 (by decide) (by decide) with h578 | h578
                · rcases m.htr 1 3 5 (by decide) (by decide) with h579 | h579
                  · linarith only [h453, h455, h577, h579, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h453, h455, h579, hc13, hlam, hphi, u3elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h582 | h582
                  · linarith only [h454, h455, h578, h582, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h454, h455, h578, h582, hc13, hlam, hphi, u3elo4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h585 | h585
                · linarith only [h0, h453, h577, h585, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h587 | h587
                  · linarith only [h0, h454, h577, h585, h587, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h454, h575, h577, h585, h587, hc23, hlam, hphi, u3elo4]
            · linarith only [h0, h454, h576, hlam]
          · linarith only [h0, h575, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h592 | h592
        · rcases m.htr 1 2 3 (by decide) (by decide) with h593 | h593
          · rcases m.htr 1 2 4 (by decide) (by decide) with h594 | h594
            · rcases m.htr 1 2 5 (by decide) (by decide) with h595 | h595
              · rcases m.htr 1 3 4 (by decide) (by decide) with h596 | h596
                · linarith only [h453, h454, h592, h595, h596, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi2]
                · linarith only [h454, h592, h595, h596, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi2]
              · linarith only [h454, h592, h594, h595, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h0, h592, h594, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
          · linarith only [h0, h592, h593, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h602 | h602
          · rcases m.htr 1 2 4 (by decide) (by decide) with h603 | h603
            · rcases m.htr 1 2 5 (by decide) (by decide) with h604 | h604
              · rcases m.htr 1 3 4 (by decide) (by decide) with h605 | h605
                · linarith only [h453, h454, h605, hlam]
                · linarith only [h453, h454, h602, h605, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h608 | h608
                · linarith only [h453, h454, h603, h604, h608, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h453, h454, h608, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h611 | h611
              · rcases m.htr 1 3 4 (by decide) (by decide) with h612 | h612
                · linarith only [h453, h592, h603, h611, h612, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h453, h592, h602, h603, h611, h612, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h615 | h615
                · linarith only [h0, h453, h603, h615, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h453, h603, h615, hc13, hlam, hphi, u3elo3]
          · linarith only [h0, h453, h602, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h619 | h619
      · rcases m.htr 0 1 5 (by decide) (by decide) with h620 | h620
        · linarith only [h453, h620, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h622 | h622
          · rcases m.htr 1 2 4 (by decide) (by decide) with h623 | h623
            · rcases m.htr 1 2 5 (by decide) (by decide) with h624 | h624
              · rcases m.htr 1 3 4 (by decide) (by decide) with h625 | h625
                · rcases m.htr 1 3 5 (by decide) (by decide) with h626 | h626
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h627 | h627
                    · linarith only [h619, h620, h626, h627, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h629 | h629
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h630 | h630
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h631 | h631
                          · linarith only [h619, h620, h623, h627, h631, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h633 | h633
                            · linarith only [h619, h620, h623, h627, h629, h633, hlam]
                            · rcases h1bigk with h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h0, hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h453, hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h620, h626, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p635_1, u3elo1]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h620, hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                rcases p635_3 (m.d 0 1) (by simp) with h641 | h641
                                · linarith only [h641, hlam, p635_0]
                                · rcases p635_3 (m.d 1 2) (by simp) with h643 | h643
                                  · rcases p635_3 (m.d 1 3) (by simp) with h644 | h644
                                    · linarith only [h622, h644, hlam]
                                    · linarith only [h453, h644, hlam]
                                  · linarith only [h643, hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h620, h626, hc01, hc12, hlam, hphi, p635_1]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                rcases p635_3 (m.d 0 1) (by simp) with h650 | h650
                                · linarith only [h0, h650, hlam]
                                · linarith only [h619, h650, hlam]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h619, h620, h623, h629, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p635_1]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h619, h623, h629, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p635_1, u3elo1]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h622, hlam, p635_1]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                rcases p635_3 (m.d 0 1) (by simp) with h657 | h657
                                · linarith only [h453, h657, hlam]
                                · linarith only [h619, h657, hlam]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h619, h620, h623, h629, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p635_1, u3elo1]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h619, hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h623, hlam, p635_1]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h625, hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h627, hlam, p635_1]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h619, h623, h627, h629, hc34, hc45, hlam, hphi, p635_1]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h624, hlam, p635_1]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h626, hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                rcases p635_3 (m.d 0 1) (by simp) with h669 | h669
                                · linarith only [h620, h669, hlam]
                                · linarith only [h619, h669, hlam]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [hlam, p635_0]
                        · linarith only [h626, h630, hc23, hlam, hphi, u3elo1]
                      · linarith only [h625, h629, hc23, hlam, hphi, u3elo1]
                  · linarith only [h453, h619, h623, h626, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · linarith only [h453, h619, h623, h625, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h677 | h677
                · rcases m.htr 1 3 5 (by decide) (by decide) with h678 | h678
                  · linarith only [h622, h624, h678, hlam]
                  · linarith only [h453, h619, h623, h678, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · linarith only [h453, h619, h623, h677, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
            · linarith only [h0, h453, h619, h623, hc02, hlam, hphi, ht23, u3elo1]
          · linarith only [h0, h622, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h684 | h684
        · linarith only [h453, h684, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h686 | h686
          · rcases m.htr 1 2 4 (by decide) (by decide) with h687 | h687
            · rcases m.htr 1 2 5 (by decide) (by decide) with h688 | h688
              · rcases m.htr 1 3 4 (by decide) (by decide) with h689 | h689
                · rcases m.htr 1 3 5 (by decide) (by decide) with h690 | h690
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h691 | h691
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h692 | h692
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h693 | h693
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h694 | h694
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h695 | h695
                            · linarith only [h686, h692, h695, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases h1bigk with h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h0, hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h453, hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h619, hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h684, hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                rcases p697_3 (m.d 0 1) (by simp) with h703 | h703
                                · linarith only [h703, hlam, p697_0]
                                · rcases p697_3 (m.d 1 2) (by simp) with h705 | h705
                                  · rcases p697_3 (m.d 1 3) (by simp) with h706 | h706
                                    · linarith only [h686, h706, hlam]
                                    · linarith only [h453, h706, hlam]
                                  · linarith only [h705, hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h684, h689, h691, hc01, hc12, hlam, hphi, p697_1]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h684, h691, hc01, hc12, hlam, hphi, p697_1]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h684, hc01, hc12, hlam, hphi, p697_1]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, p697_1, u3elo1]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h686, hlam, p697_1]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h687, h694, h695, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p697_1, u3elo1]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h684, hc01, hlam, hphi, ht12, ht23, p697_1, u3elo1]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h689, hc01, hlam, hphi, ht12, ht23, p697_1, u3elo1]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h687, hlam, p697_1]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h689, hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h684, h689, hc01, hlam, hphi, ht12, ht23, p697_1, u3elo1]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h690, hc01, hlam, hphi, ht12, ht23, p697_1, u3elo1]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h688, hlam, p697_1]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h690, hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [h691, hlam, p697_0]
                              · have p697_0 := h697c.1
                                have p697_1 := h697c.2.1
                                have p697_2 := h697c.2.2.1
                                have p697_3 := h697c.2.2.2
                                linarith only [hlam, p697_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h729 | h729
                            · linarith only [h689, h694, h729, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · rcases h1bigk with h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h0, hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h453, hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h619, hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h684, hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                rcases p731_3 (m.d 0 1) (by simp) with h737 | h737
                                · linarith only [h737, hlam, p731_0]
                                · rcases p731_3 (m.d 1 2) (by simp) with h739 | h739
                                  · rcases p731_3 (m.d 1 3) (by simp) with h740 | h740
                                    · linarith only [h686, h740, hlam]
                                    · linarith only [h453, h740, hlam]
                                  · linarith only [h739, hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h453, hc01, hc12, hlam, hphi, p731_1]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h684, h691, hc01, hc12, hlam, hphi, p731_1]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h684, hc01, hc12, hlam, hphi, p731_1]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, p731_1, u3elo1]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h686, hlam, p731_1]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h684, h691, hc01, hlam, hphi, ht12, ht23, p731_1, u3elo1]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h684, hc01, hlam, hphi, ht12, ht23, p731_1, u3elo1]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h689, hc01, hlam, hphi, ht12, ht23, p731_1, u3elo1]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h687, hlam, p731_1]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h689, hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h684, h689, hc01, hlam, hphi, ht12, ht23, p731_1, u3elo1]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h690, hc01, hlam, hphi, ht12, ht23, p731_1, u3elo1]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h688, hlam, p731_1]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h690, hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [h691, hlam, p731_0]
                              · have p731_0 := h731c.1
                                have p731_1 := h731c.2.1
                                have p731_2 := h731c.2.2.1
                                have p731_3 := h731c.2.2.2
                                linarith only [hlam, p731_0]
                        · linarith only [h690, h693, hc23, hlam, hphi, u3elo1]
                      · linarith only [h689, h692, hc23, hlam, hphi, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h765 | h765
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h766 | h766
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h767 | h767
                          · linarith only [h619, h691, h767, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h769 | h769
                            · linarith only [h619, h691, h769, hc01, hlam, hphi, ht12, ht23, u3elo3]
                            · rcases h1bigk with h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [hlam, p771_0]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [h0, hlam, p771_0]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [h453, hlam, p771_0]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [h619, hlam, p771_0]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [h684, hlam, p771_0]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                rcases p771_3 (m.d 0 1) (by simp) with h777 | h777
                                · linarith only [h777, hlam, p771_0]
                                · rcases p771_3 (m.d 1 2) (by simp) with h779 | h779
                                  · rcases p771_3 (m.d 1 3) (by simp) with h780 | h780
                                    · linarith only [h686, h780, hlam]
                                    · linarith only [h453, h780, hlam]
                                  · linarith only [h779, hlam, p771_0]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [hlam, p771_0]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [h453, hc01, hc12, hlam, hphi, p771_1]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [h619, hc01, hc12, hlam, hphi, p771_1]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [h684, hc01, hc12, hlam, hphi, p771_1]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, p771_1, u3elo1]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [h686, hlam, p771_1]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [hlam, p771_0]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [h619, hc01, hlam, hphi, ht12, ht23, p771_1, u3elo1]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p771_1, u3elo1, u5ehi1]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [h691, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p771_1]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [h687, hlam, p771_1]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [h689, hlam, p771_0]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [hlam, p771_0]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [h691, hlam, p771_1]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [h690, hc01, hlam, hphi, ht12, ht23, p771_1, u3elo1]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [h688, hlam, p771_1]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [h690, hlam, p771_0]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [h619, h690, hc01, hlam, hphi, ht12, ht23, p771_1, u3elo1]
                              · have p771_0 := h771c.1
                                have p771_1 := h771c.2.1
                                have p771_2 := h771c.2.2.1
                                have p771_3 := h771c.2.2.2
                                linarith only [hlam, p771_0]
                        · linarith only [h690, h766, hc23, hlam, hphi, u3elo1]
                      · linarith only [h689, h765, hc23, hlam, hphi, u3elo1]
                  · linarith only [h453, h690, hc01, hlam, hphi, ht12, ht23, u3elo4]
                · linarith only [h453, h689, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h807 | h807
                · rcases m.htr 1 3 5 (by decide) (by decide) with h808 | h808
                  · linarith only [h686, h688, h808, hlam]
                  · linarith only [h453, h808, hc01, hlam, hphi, ht12, ht23, u3elo4]
                · linarith only [h453, h807, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h812 | h812
              · rcases m.htr 1 3 4 (by decide) (by decide) with h813 | h813
                · linarith only [h686, h687, h813, hlam]
                · linarith only [h453, h813, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h816 | h816
                · linarith only [h686, h687, h816, hlam]
                · linarith only [h453, h816, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · linarith only [h0, h686, hc01, hlam, hphi, ht12, ht23, u3elo2]

end R2N4
