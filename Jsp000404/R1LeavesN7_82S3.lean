import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_I_L_0_L_R_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
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
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h3, h8, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                    · linarith only [h0, h10, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                    · linarith only [h0, h10, h2, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
                · linarith only [h0, h2, h7, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                  · linarith only [h15, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h17, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                    · linarith only [h0, h17, h2, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
                · linarith only [h0, h14, h2, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi1]
            · linarith only [h1, h5, hc12, hlam, hphi, u2elo0]
          · linarith only [h0, h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
          · linarith only [h23, h3, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
          · linarith only [h0, h23, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
        · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
          · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
            · rcases m.htr 1 3 5 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 4 5 (by decide) (by decide) with h30 | h30
                · linarith only [h2, h27, h30, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h32 | h32
                  · linarith only [h26, h32, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h34 | h34
                    · linarith only [h0, h2, h34, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
                      · linarith only [h0, h2, h26, h29, h36, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi2]
                      · rcases h5bigk with h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [hlam, p38_0]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, p38_1, u2elo0, u5ehi1]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, p38_1, u2elo0, u5ehi2]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h1, h32, h34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p38_1, u2elo0, u4ehi2]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h2, hlam, p38_0]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h1, h28, h34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p38_1, u2elo1, u4ehi2]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [hlam, p38_0]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h28, h34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p38_1, u2elo1, u4ehi2]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h26, h29, h32, h34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p38_1, u2elo1, u4ehi2]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h30, hlam, p38_0]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h1, hlam, p38_1]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h28, hlam, p38_1]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [hlam, p38_0]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h32, hlam, p38_1]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h34, hlam, p38_0]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h1, h26, h29, h34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p38_1, u2elo1, u4ehi2]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h29, hlam, p38_1]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h26, h29, h34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p38_1, u2elo1, u4ehi2]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [hlam, p38_0]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h36, hlam, p38_0]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h1, h34, hc45, hlam, hphi, p38_1, u4ehi2]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h28, h34, hc45, hlam, hphi, p38_1, u4ehi2]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h34, hc45, hlam, hphi, p38_1, u4ehi2]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [h32, h34, hc45, hlam, hphi, p38_1, u4ehi2]
                        · have p38_0 := h38c.1
                          have p38_1 := h38c.2.1
                          have p38_2 := h38c.2.2.1
                          have p38_3 := h38c.2.2.2
                          linarith only [hlam, p38_0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h64 | h64
                · linarith only [h0, h2, h27, h64, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h66 | h66
                  · linarith only [h26, h66, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h68 | h68
                    · linarith only [h0, h2, h68, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h70 | h70
                      · rcases h5bigk with h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [hlam, p71_0]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, p71_1, u2elo0, u5ehi1]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, p71_1, u2elo0, u5ehi2]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [h2, h70, hlam, p71_1]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [h2, hlam, p71_0]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [h1, h28, h68, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p71_1, u2elo1, u4ehi2]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [hlam, p71_0]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [h28, h68, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p71_1, u2elo1, u4ehi2]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [h29, hlam, p71_0]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [h64, hlam, p71_0]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [h1, hlam, p71_1]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [h28, hlam, p71_1]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [hlam, p71_0]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [h66, hlam, p71_1]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [h68, hlam, p71_0]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          rcases p71_3 (m.d 0 5) (by simp) with h87 | h87
                          · linarith only [h87, hlam, p71_0]
                          · rcases p71_3 (m.d 1 5) (by simp) with h89 | h89
                            · linarith only [h29, h89, hlam]
                            · rcases p71_3 (m.d 2 5) (by simp) with h91 | h91
                              · linarith only [h66, h91, hlam]
                              · rcases p71_3 (m.d 3 5) (by simp) with h93 | h93
                                · rcases p71_3 (m.d 4 5) (by simp) with h94 | h94
                                  · linarith only [h70, h94, hlam]
                                  · linarith only [h2, h94, hlam]
                                · linarith only [h93, hlam, p71_0]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          rcases p71_3 (m.d 0 5) (by simp) with h98 | h98
                          · linarith only [h1, h98, hlam, hphi, ht01, ht0b, ht12, ht5b, p71_1, u2elo0, u5ehi1]
                          · rcases p71_3 (m.d 1 5) (by simp) with h100 | h100
                            · linarith only [h100, h29, hlam]
                            · rcases p71_3 (m.d 2 5) (by simp) with h102 | h102
                              · linarith only [h102, h66, hlam]
                              · rcases p71_3 (m.d 3 5) (by simp) with h104 | h104
                                · rcases p71_3 (m.d 4 5) (by simp) with h105 | h105
                                  · linarith only [h105, h70, hlam]
                                  · linarith only [h105, h64, hlam]
                                · linarith only [h104, h29, hlam]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          rcases p71_3 (m.d 0 5) (by simp) with h109 | h109
                          · linarith only [h1, h109, hlam, hphi, ht01, ht0b, ht12, ht5b, p71_1, u2elo0, u5ehi2]
                          · linarith only [h1, h109, hlam]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [hlam, p71_0]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [h0, h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p71_1, u4ehi2]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [h1, h68, hc45, hlam, hphi, p71_1, u4ehi2]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [h27, h64, hc45, hlam, hphi, p71_1, u4ehi2]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [h68, hc45, hlam, hphi, p71_1, u4ehi2]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [h70, hlam, p71_1]
                        · have p71_0 := h71c.1
                          have p71_1 := h71c.2.1
                          have p71_2 := h71c.2.2.1
                          have p71_3 := h71c.2.2.2
                          linarith only [hlam, p71_0]
                      · rcases h5bigk with h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [hlam, p119_0]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h1, h27, h64, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p119_1, u2elo0, u4ehi2]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h1, h68, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p119_1, u2elo0, u4ehi2]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, p119_1, u2elo0, u5ehi3]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h2, hlam, p119_0]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h1, h28, h68, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p119_1, u2elo1, u4ehi2]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [hlam, p119_0]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h28, h68, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p119_1, u2elo1, u4ehi2]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h29, hlam, p119_0]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h64, hlam, p119_0]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h1, hlam, p119_1]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h28, hlam, p119_1]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [hlam, p119_0]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h66, hlam, p119_1]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h68, hlam, p119_0]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h1, h68, h70, hc45, hlam, hphi, p119_1, u4ehi2]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h28, h68, h70, hc45, hlam, hphi, p119_1, u4ehi2]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h68, h70, hc45, hlam, hphi, p119_1, u4ehi2]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [hlam, p119_0]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h70, hlam, p119_0]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h1, h68, hc45, hlam, hphi, p119_1, u4ehi2]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h28, h68, hc45, hlam, hphi, p119_1, u4ehi2]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h68, hc45, hlam, hphi, p119_1, u4ehi2]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [h26, h29, hc23, hc45, hlam, hphi, ht34, p119_1]
                        · have p119_0 := h119c.1
                          have p119_1 := h119c.2.1
                          have p119_2 := h119c.2.2.1
                          have p119_3 := h119c.2.2.2
                          linarith only [hlam, p119_0]
            · linarith only [h1, h28, hc12, hlam, hphi, u2elo0]
          · linarith only [h0, h26, h27, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h147 | h147
          · linarith only [h147, h26, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
          · linarith only [h0, h147, hc12, hlam, hphi, u2elo0]
    · linarith only [h0, h1, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h151 | h151
    · linarith only [h0, h151, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h153 | h153
      · rcases m.htr 1 2 3 (by decide) (by decide) with h154 | h154
        · rcases m.htr 1 2 4 (by decide) (by decide) with h155 | h155
          · linarith only [h0, h155, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h157 | h157
            · linarith only [h151, h155, h157, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h159 | h159
              · linarith only [h154, h155, h159, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h161 | h161
                · rcases m.htr 2 3 5 (by decide) (by decide) with h162 | h162
                  · linarith only [h154, h155, h159, h162, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h164 | h164
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h165 | h165
                      · rcases h5bigk with h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h151, h157, h164, hc12, hlam, hphi, p166_1, u2elo3]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h151, hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h151, h162, hlam, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h151, h164, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p166_1, u2elo3, u4ehi4]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h157, h164, hlam, hphi, ht01, ht0b, ht12, ht5b, p166_1, u2elo3, u5ehi0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h157, hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h159, hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h157, h164, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p166_1, u2elo3, u4ehi4]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h153, h164, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p166_1, u2elo3, u4ehi4]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h164, hlam, hphi, ht01, ht0b, ht12, ht5b, p166_1, u2elo3, u5ehi1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h162, hlam, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h164, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p166_1, u2elo3, u4ehi4]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          rcases p166_3 (m.d 0 5) (by simp) with h182 | h182
                          · linarith only [h182, hlam, p166_0]
                          · rcases p166_3 (m.d 1 5) (by simp) with h184 | h184
                            · linarith only [h159, h184, hlam]
                            · linarith only [h154, h157, h165, h184, hc23, hc34, hlam, hphi, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h154, h157, h165, hc23, hc34, hlam, hphi, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h151, h165, hc02, hc34, hlam, hphi, ht23, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          rcases p166_3 (m.d 0 5) (by simp) with h190 | h190
                          · linarith only [h151, h162, h190, hlam]
                          · linarith only [h153, h190, hlam]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h153, hlam, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h161, hlam, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h164, hlam, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h165, hlam, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hlam, p166_0]
                      · linarith only [h0, h153, h165, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                    · linarith only [h0, h153, h164, hlam]
                · linarith only [h0, h153, h161, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h201 | h201
          · linarith only [h0, h154, h201, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h203 | h203
            · linarith only [h151, h154, h203, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h205 | h205
              · rcases m.htr 1 4 5 (by decide) (by decide) with h206 | h206
                · rcases m.htr 2 3 5 (by decide) (by decide) with h207 | h207
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h208 | h208
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h209 | h209
                      · rcases h5bigk with h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [hlam, p210_0]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h151, h203, h207, hc12, hlam, hphi, p210_1, u2elo2]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h151, hlam, p210_0]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h151, h207, h209, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p210_1, u2elo2, u4ehi4]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h151, h207, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p210_1, u2elo2, u4ehi4]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h153, h203, h207, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p210_1, u2elo2, u4ehi4]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [hlam, p210_0]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h203, hlam, p210_0]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h203, h207, h209, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p210_1, u2elo2, u4ehi4]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h203, h207, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p210_1, u2elo2, u4ehi4]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h153, h207, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p210_1, u2elo2, u4ehi4]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h207, hlam, hphi, ht01, ht0b, ht12, ht5b, p210_1, u2elo2, u5ehi1]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [hlam, p210_0]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h207, h209, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p210_1, u2elo2, u4ehi4]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h207, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p210_1, u2elo2, u4ehi4]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h153, h205, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p210_1, u4ehi4]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h205, hlam, p210_1]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h207, hlam, p210_0]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [hlam, p210_0]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h154, h205, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p210_1, u2elo2, u4ehi4]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h153, hlam, p210_1]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h206, hlam, p210_1]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h208, hlam, p210_1]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [h209, hlam, p210_1]
                        · have p210_0 := h210c.1
                          have p210_1 := h210c.2.1
                          have p210_2 := h210c.2.2.1
                          have p210_3 := h210c.2.2.2
                          linarith only [hlam, p210_0]
                      · linarith only [h0, h153, h209, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                    · linarith only [h0, h153, h208, hlam]
                  · linarith only [h154, h205, h207, hlam]
                · linarith only [h0, h153, h206, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h240 | h240
                · rcases m.htr 2 3 5 (by decide) (by decide) with h241 | h241
                  · linarith only [h154, h205, h241, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h243 | h243
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h244 | h244
                      · rcases h5bigk with h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [hlam, p245_0]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [h151, h243, hlam, hphi, ht01, ht0b, ht12, ht5b, p245_1, u2elo3, u5ehi1]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [h151, hlam, p245_0]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [h151, h154, h241, h243, hc12, hlam, hphi, p245_1, u2elo3]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [h151, h243, hlam, hphi, ht01, ht0b, ht12, ht5b, p245_1, u2elo3, u5ehi4]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [h153, h203, h243, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p245_1, u2elo3, u4ehi4]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [hlam, p245_0]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [h203, hlam, p245_0]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [h205, hlam, p245_0]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [h203, h243, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p245_1, u2elo3, u4ehi4]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [h153, h243, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p245_1, u2elo3, u4ehi4]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [h243, hlam, hphi, ht01, ht0b, ht12, ht5b, p245_1, u2elo3, u5ehi1]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [hlam, p245_0]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [h241, hlam, p245_1]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [h243, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p245_1, u2elo3, u4ehi4]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          rcases p245_3 (m.d 0 5) (by simp) with h261 | h261
                          · linarith only [h261, hlam, p245_0]
                          · rcases p245_3 (m.d 1 5) (by simp) with h263 | h263
                            · linarith only [h205, h263, hlam]
                            · rcases p245_3 (m.d 2 5) (by simp) with h265 | h265
                              · linarith only [h241, h265, hlam]
                              · linarith only [h151, h265, hlam]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          rcases p245_3 (m.d 0 5) (by simp) with h268 | h268
                          · linarith only [h151, h240, h243, h268, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p245_1, u2elo3, u4ehi4]
                          · rcases p245_3 (m.d 1 5) (by simp) with h270 | h270
                            · linarith only [h205, h270, hlam]
                            · rcases p245_3 (m.d 2 5) (by simp) with h272 | h272
                              · linarith only [h241, h272, hlam]
                              · linarith only [h203, h272, hlam]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [h151, h244, hc02, hc34, hlam, hphi, ht23, p245_1]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [hlam, p245_0]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          rcases p245_3 (m.d 0 5) (by simp) with h277 | h277
                          · linarith only [h0, h153, h154, h241, h277, hc12, hlam, hphi, u2elo3]
                          · linarith only [h153, h277, hlam]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [h153, hlam, p245_1]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [h240, hlam, p245_1]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [h243, hlam, p245_1]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [h244, hlam, p245_1]
                        · have p245_0 := h245c.1
                          have p245_1 := h245c.2.1
                          have p245_2 := h245c.2.2.1
                          have p245_3 := h245c.2.2.2
                          linarith only [hlam, p245_0]
                      · linarith only [h0, h153, h244, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                    · linarith only [h0, h153, h243, hlam]
                · linarith only [h0, h153, h240, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h288 | h288
        · rcases m.htr 1 2 4 (by decide) (by decide) with h289 | h289
          · linarith only [h0, h289, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h291 | h291
            · linarith only [h151, h153, h289, h291, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h293 | h293
              · linarith only [h288, h289, h293, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h295 | h295
                · linarith only [h153, h289, h295, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h297 | h297
                  · linarith only [h288, h289, h293, h297, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h299 | h299
                    · linarith only [h289, h295, h299, hc12, hlam, hphi, u2elo3]
                    · linarith only [h288, h289, h299, hc23, hc45, hlam, hphi, ht34]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h302 | h302
          · linarith only [h288, h302, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h304 | h304
            · linarith only [h151, h288, h304, hc02, hlam, hphi, u2elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h306 | h306
              · rcases m.htr 1 4 5 (by decide) (by decide) with h307 | h307
                · linarith only [h153, h302, h307, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h309 | h309
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h310 | h310
                    · linarith only [h302, h307, h310, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h312 | h312
                      · linarith only [h0, h310, h312, hc02, hc34, hlam, hphi, ht23]
                      · rcases h5bigk with h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [hlam, p314_0]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h151, h309, hlam, hphi, ht01, ht0b, ht12, ht5b, p314_1, u2elo2, u5ehi1]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h151, hlam, p314_0]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h151, h309, h312, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p314_1, u2elo2, u4ehi3]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h153, hlam, p314_0]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h153, h304, h309, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p314_1, u2elo2, u4ehi0]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [hlam, p314_0]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h304, hlam, p314_0]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h304, h309, h312, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p314_1, u2elo2, u4ehi3]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h307, hlam, p314_0]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h153, h309, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p314_1, u2elo2, u4ehi0]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h309, hlam, hphi, ht01, ht0b, ht12, ht5b, p314_1, u2elo2, u5ehi1]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [hlam, p314_0]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h309, h312, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p314_1, u2elo2, u4ehi3]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h310, hlam, p314_0]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h153, h306, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p314_1, u4ehi0]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h306, hlam, p314_1]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h309, hlam, p314_0]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [hlam, p314_0]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h312, hlam, p314_0]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h153, hc45, hlam, hphi, p314_1, u4ehi0]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h307, hc45, hlam, hphi, p314_1, u4ehi1]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h151, hc02, hc45, hlam, hphi, ht23, ht34, p314_1]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [h312, hc45, hlam, hphi, p314_1, u4ehi3]
                        · have p314_0 := h314c.1
                          have p314_1 := h314c.2.1
                          have p314_2 := h314c.2.2.1
                          have p314_3 := h314c.2.2.2
                          linarith only [hlam, p314_0]
                  · linarith only [h288, h306, h309, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h341 | h341
                · linarith only [h153, h302, h341, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h343 | h343
                  · linarith only [h288, h306, h343, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h345 | h345
                    · linarith only [h153, h345, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h347 | h347
                      · linarith only [h0, h345, h347, hc02, hc34, hlam, hphi, ht23]
                      · rcases h5bigk with h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h151, h341, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p349_1, u2elo4, u4ehi1]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h151, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h151, h288, h343, hc12, hlam, hphi, p349_1, u2elo4]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h153, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h153, h304, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p349_1, u2elo4, u4ehi0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h304, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h306, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h341, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h153, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p349_1, u2elo4, u4ehi0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p349_1, u2elo4, u5ehi1]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h343, hlam, p349_1]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h345, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h153, h347, hc45, hlam, hphi, p349_1, u4ehi0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h341, h347, hc45, hlam, hphi, p349_1, u4ehi1]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h151, h347, hc02, hc45, hlam, hphi, ht23, ht34, p349_1]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h347, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h153, hc45, hlam, hphi, p349_1, u4ehi0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h341, hc45, hlam, hphi, p349_1, u4ehi1]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h288, h343, hc12, hc45, hlam, hphi, ht23, ht34, p349_1]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h288, h306, hc12, hc45, hlam, hphi, ht23, ht34, p349_1]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [hlam, p349_0]

theorem r1l7_11_12_14_25_L_R_L_R_L_I_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h5, h7, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                      · linarith only [h11, h6, h8, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                        · linarith only [h0, h10, h13, h5, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                        · rcases h4bigk with h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            rcases p15_3 (m.d 0 4) (by simp) with h17 | h17
                            · rcases p15_3 (m.d 1 4) (by simp) with h18 | h18
                              · linarith only [h1, h18, hlam]
                              · rcases p15_3 (m.d 2 4) (by simp) with h20 | h20
                                · linarith only [h2, h20, hlam]
                                · rcases p15_3 (m.d 3 4) (by simp) with h22 | h22
                                  · linarith only [h22, h3, hlam]
                                  · rcases p15_3 (m.d 4 5) (by simp) with h24 | h24
                                    · linarith only [h24, h4, hlam]
                                    · linarith only [h24, h8, hlam]
                            · linarith only [h1, h17, hlam]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            rcases p15_3 (m.d 0 4) (by simp) with h28 | h28
                            · rcases p15_3 (m.d 1 4) (by simp) with h29 | h29
                              · linarith only [h1, h29, hlam]
                              · linarith only [h29, h6, hlam]
                            · linarith only [h2, h28, hlam]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            rcases p15_3 (m.d 0 4) (by simp) with h33 | h33
                            · rcases p15_3 (m.d 1 4) (by simp) with h34 | h34
                              · linarith only [h1, h34, hlam]
                              · linarith only [h34, h7, hlam]
                            · linarith only [h3, h33, hlam]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h0, h2, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p15_1, u1ehi3]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h1, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h8, hc24, hc45, hlam, hphi, p15_1]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h0, h2, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h8, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h2, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h6, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h0, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h11, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h3, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h7, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h10, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h13, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h4, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p15_1, u1ehi3]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15_1, u2ehi3]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            rcases p15_3 (m.d 0 4) (by simp) with h57 | h57
                            · rcases p15_3 (m.d 1 4) (by simp) with h58 | h58
                              · linarith only [h58, h8, hlam]
                              · linarith only [h58, h7, hlam]
                            · linarith only [h3, h57, hlam]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [hlam, p15_0]
                    · linarith only [h0, h10, h5, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h64 | h64
                  · linarith only [h1, h64, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                    · linarith only [h5, h66, h7, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h68 | h68
                      · linarith only [h64, h68, h7, hc24, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h70 | h70
                        · linarith only [h3, h64, h7, h70, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                        · linarith only [h0, h2, h4, h7, h70, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
              · linarith only [h0, h2, h5, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
              · linarith only [h5, h74, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                · rcases m.htr 1 4 5 (by decide) (by decide) with h77 | h77
                  · linarith only [h1, h77, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h80 | h80
                      · linarith only [h0, h2, h74, h77, h80, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                      · linarith only [h74, h80, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h5, h76, h79, hc13, hlam, hphi, u1ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h84 | h84
                  · linarith only [h1, h84, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                    · linarith only [h5, h76, h86, hc23, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h5, h86, hc34, hlam, hphi, ht12, ht23, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h89 | h89
            · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
              · rcases m.htr 1 3 4 (by decide) (by decide) with h91 | h91
                · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
                  · linarith only [h1, h4, h92, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h95 | h95
                      · linarith only [h89, h94, h95, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h97 | h97
                        · linarith only [h0, h1, h4, h89, h94, h97, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                        · rcases h4bigk with h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h4, hc45, hlam, hphi, ht12, ht23, ht34, p99_1, u1ehi3]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h4, hc24, hc45, hlam, hphi, p99_1]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h4, hc34, hc45, hlam, hphi, p99_1]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h4, hlam, p99_0]
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
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p99_1, u2ehi3]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h1, h4, hc34, hc45, hlam, hphi, p99_1]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h92, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h2, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h90, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h2, h4, hc34, hc45, hlam, hphi, p99_1]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h95, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h3, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h91, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h94, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h97, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h1, hc45, hlam, hphi, ht12, ht23, ht34, p99_1, u1ehi3]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p99_1, u1ehi3]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [hc45, hlam, hphi, ht23, ht34, p99_1, u2ehi3]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            rcases p99_3 (m.d 0 4) (by simp) with h123 | h123
                            · linarith only [h123, h4, hlam]
                            · linarith only [h123, h3, hlam]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [hlam, p99_0]
                    · linarith only [h3, h4, h94, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h3, h4, h91, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · linarith only [h2, h4, h90, hc45, hlam, hphi, ht23, ht34, u2ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h130 | h130
              · linarith only [h130, h89, hc23, hlam, hphi, u2ehi3]
              · linarith only [h130, h2, h4, hc45, hlam, hphi, ht23, ht34, u2ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h133 | h133
          · rcases m.htr 1 2 3 (by decide) (by decide) with h134 | h134
            · rcases m.htr 1 2 4 (by decide) (by decide) with h135 | h135
              · rcases m.htr 1 3 4 (by decide) (by decide) with h136 | h136
                · linarith only [h133, h134, h136, h3, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h138 | h138
                  · linarith only [h1, h138, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · linarith only [h133, h138, h3, hc34, hlam, hphi, ht12, ht23, u1ehi3]
              · linarith only [h0, h134, h135, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h142 | h142
              · linarith only [h134, h142, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h144 | h144
                · linarith only [h0, h133, h142, h144, h2, h3, hc01, hc13, hlam, hphi, ht0b, ht5b, u1ehi1, u5ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h146 | h146
                  · linarith only [h1, h146, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · linarith only [h133, h146, h3, hc34, hlam, hphi, ht12, ht23, u1ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h149 | h149
            · rcases m.htr 1 2 4 (by decide) (by decide) with h150 | h150
              · rcases m.htr 1 3 4 (by decide) (by decide) with h151 | h151
                · linarith only [h1, h151, h3, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h153 | h153
                  · linarith only [h1, h153, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                    · linarith only [h0, h149, h155, h3, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h157 | h157
                      · linarith only [h0, h133, h150, h157, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h159 | h159
                        · linarith only [h1, h133, h151, h159, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                        · linarith only [h151, h159, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · linarith only [h133, h150, h2, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h163 | h163
              · linarith only [h149, h163, hc23, hlam, hphi, u2ehi3]
              · linarith only [h133, h163, h2, hc45, hlam, hphi, ht23, ht34, u2ehi1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h166 | h166
        · rcases m.htr 0 4 5 (by decide) (by decide) with h167 | h167
          · rcases m.htr 1 2 3 (by decide) (by decide) with h168 | h168
            · linarith only [h0, h168, h2, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h170 | h170
              · linarith only [h0, h170, h2, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
                · rcases m.htr 1 4 5 (by decide) (by decide) with h173 | h173
                  · linarith only [h1, h173, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · linarith only [h167, h173, h2, hc24, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h176 | h176
                  · linarith only [h1, h176, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · linarith only [h167, h176, h2, hc24, hlam, hphi, ht12, u1ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
            · linarith only [h0, h167, h179, h2, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
              · linarith only [h0, h167, h181, h2, hc45, hlam, hphi, ht23, ht34, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h183 | h183
                · rcases m.htr 1 4 5 (by decide) (by decide) with h184 | h184
                  · linarith only [h1, h167, h184, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h186 | h186
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h187 | h187
                      · linarith only [h167, h186, h187, h2, hc23, hlam, hphi, u2ehi0]
                      · linarith only [h0, h187, h2, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h1, h167, h183, h186, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h166, h167, h183, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h192 | h192
          · rcases m.htr 1 2 3 (by decide) (by decide) with h193 | h193
            · linarith only [h0, h193, h2, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h195 | h195
              · linarith only [h0, h195, h2, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h197 | h197
                · linarith only [h166, h192, h197, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h199 | h199
                  · linarith only [h1, h199, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · linarith only [h166, h192, h199, hc34, hlam, hphi, ht12, ht23, u1ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h202 | h202
            · linarith only [h0, h192, h2, h202, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h204 | h204
              · linarith only [h0, h192, h2, h204, hc45, hlam, hphi, ht23, ht34, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                · linarith only [h1, h166, h206, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h208 | h208
                  · linarith only [h1, h192, h208, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h210 | h210
                    · linarith only [h202, h206, h210, hc23, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h202, h210, hc34, hlam, hphi, ht12, ht23, u1ehi1]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h214 | h214
    · linarith only [h0, h214, hc12, hlam, hphi, u1ehi3]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h216 | h216
      · rcases m.htr 0 3 4 (by decide) (by decide) with h217 | h217
        · rcases m.htr 0 4 5 (by decide) (by decide) with h218 | h218
          · rcases m.htr 1 2 3 (by decide) (by decide) with h219 | h219
            · rcases m.htr 1 2 4 (by decide) (by decide) with h220 | h220
              · rcases m.htr 1 3 4 (by decide) (by decide) with h221 | h221
                · rcases m.htr 1 4 5 (by decide) (by decide) with h222 | h222
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h223 | h223
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h224 | h224
                      · linarith only [h216, h224, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h226 | h226
                        · linarith only [h223, h224, h226, hlam]
                        · rcases h4bigk with h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            linarith only [hlam, p228_0]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            linarith only [h214, hlam, p228_1]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            rcases p228_3 (m.d 0 4) (by simp) with h231 | h231
                            · rcases p228_3 (m.d 1 4) (by simp) with h232 | h232
                              · rcases p228_3 (m.d 2 4) (by simp) with h233 | h233
                                · linarith only [h216, h233, hlam]
                                · rcases p228_3 (m.d 3 4) (by simp) with h235 | h235
                                  · linarith only [h217, h235, hlam]
                                  · rcases p228_3 (m.d 4 5) (by simp) with h237 | h237
                                    · linarith only [h218, h237, hlam]
                                    · linarith only [h224, h237, hlam]
                              · linarith only [h220, h232, hlam]
                            · linarith only [h216, h231, hlam]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            rcases p228_3 (m.d 0 4) (by simp) with h242 | h242
                            · rcases p228_3 (m.d 1 4) (by simp) with h243 | h243
                              · rcases p228_3 (m.d 2 4) (by simp) with h244 | h244
                                · linarith only [h216, h244, hlam]
                                · linarith only [h223, h244, hlam]
                              · linarith only [h221, h243, hlam]
                            · linarith only [h217, h242, hlam]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            linarith only [h217, h224, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p228_1, u2ehi3]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            linarith only [h214, h219, h221, hc12, hlam, hphi, p228_1, u1ehi0]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            linarith only [hlam, p228_0]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            rcases p228_3 (m.d 0 4) (by simp) with h252 | h252
                            · linarith only [h214, h252, hlam]
                            · linarith only [h216, h252, hlam]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            rcases p228_3 (m.d 0 4) (by simp) with h255 | h255
                            · linarith only [h214, h255, hlam]
                            · linarith only [h217, h255, hlam]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            linarith only [h219, h221, h224, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p228_1, u2ehi3]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            linarith only [h216, hlam, p228_0]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            linarith only [h220, hlam, p228_0]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            linarith only [hlam, p228_0]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            linarith only [h218, h224, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p228_1]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            linarith only [h224, hlam, p228_0]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            linarith only [h217, hlam, p228_0]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            linarith only [h221, hlam, p228_0]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            linarith only [h223, hlam, p228_0]
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
                            linarith only [h222, hlam, p228_0]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            linarith only [h218, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p228_1, u2ehi3]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            rcases p228_3 (m.d 0 4) (by simp) with h272 | h272
                            · rcases p228_3 (m.d 1 4) (by simp) with h273 | h273
                              · rcases p228_3 (m.d 2 4) (by simp) with h274 | h274
                                · linarith only [h224, h274, hlam]
                                · linarith only [h223, h274, hlam]
                              · linarith only [h221, h273, hlam]
                            · linarith only [h217, h272, hlam]
                          · have p228_0 := h228c.1
                            have p228_1 := h228c.2.1
                            have p228_2 := h228c.2.2.1
                            have p228_3 := h228c.2.2.2
                            linarith only [hlam, p228_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h280 | h280
                      · linarith only [h0, h216, h280, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h282 | h282
                        · linarith only [h219, h221, h223, h280, h282, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h223, h282, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h214, h218, h222, hlam]
                · linarith only [h214, h217, h218, h221, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
              · linarith only [h0, h220, hc24, hlam, hphi, ht12, u1ehi0]
            · linarith only [h0, h216, h218, h219, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h289 | h289
            · rcases m.htr 1 2 4 (by decide) (by decide) with h290 | h290
              · rcases m.htr 1 3 4 (by decide) (by decide) with h291 | h291
                · rcases m.htr 1 4 5 (by decide) (by decide) with h292 | h292
                  · linarith only [h214, h218, h289, h291, h292, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h214, h292, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                · linarith only [h217, h218, h291, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · linarith only [h0, h216, h290, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
            · linarith only [h0, h289, hc23, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h298 | h298
          · rcases m.htr 1 2 3 (by decide) (by decide) with h299 | h299
            · rcases m.htr 1 2 4 (by decide) (by decide) with h300 | h300
              · rcases m.htr 1 3 4 (by decide) (by decide) with h301 | h301
                · linarith only [h217, h298, h301, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h303 | h303
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h304 | h304
                    · linarith only [h299, h301, h304, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h306 | h306
                      · linarith only [h216, h306, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · linarith only [h214, h298, h301, h306, hc34, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h214, h298, h303, hlam]
              · linarith only [h0, h300, hc24, hlam, hphi, ht12, u1ehi0]
            · linarith only [h0, h216, h298, h299, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h312 | h312
            · rcases m.htr 1 2 4 (by decide) (by decide) with h313 | h313
              · rcases m.htr 1 3 4 (by decide) (by decide) with h314 | h314
                · rcases m.htr 1 4 5 (by decide) (by decide) with h315 | h315
                  · linarith only [h214, h298, h315, hc14, hlam, hphi, u1ehi0]
                  · linarith only [h214, h315, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h318 | h318
                  · linarith only [h214, h298, h318, hc14, hlam, hphi, u1ehi0]
                  · linarith only [h214, h318, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
              · linarith only [h0, h216, h313, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
            · linarith only [h0, h312, hc23, hlam, hphi, ht12, u1ehi0]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h323 | h323
        · rcases m.htr 0 4 5 (by decide) (by decide) with h324 | h324
          · rcases m.htr 1 2 3 (by decide) (by decide) with h325 | h325
            · rcases m.htr 1 2 4 (by decide) (by decide) with h326 | h326
              · linarith only [h0, h216, h326, hc12, hlam, hphi, u1ehi0]
              · linarith only [h325, h326, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h325, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h330 | h330
            · rcases m.htr 1 2 4 (by decide) (by decide) with h331 | h331
              · linarith only [h0, h216, h331, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h331, hc24, hlam, hphi, ht12, u1ehi0]
            · linarith only [h0, h330, hc23, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h335 | h335
          · rcases m.htr 1 2 3 (by decide) (by decide) with h336 | h336
            · rcases m.htr 1 2 4 (by decide) (by decide) with h337 | h337
              · linarith only [h0, h216, h337, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h337, hc24, hlam, hphi, ht12, u1ehi0]
            · linarith only [h0, h336, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h341 | h341
            · rcases m.htr 1 2 4 (by decide) (by decide) with h342 | h342
              · linarith only [h0, h216, h342, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h342, hc24, hlam, hphi, ht12, u1ehi0]
            · linarith only [h0, h341, hc23, hlam, hphi, ht12, u1ehi0]

end R2N4
