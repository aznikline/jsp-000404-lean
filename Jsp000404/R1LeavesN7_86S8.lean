import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_15_H_L_L_I_L_0 (m : N7Model)
    (hb2 : CMSig2_7_H_L m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · linarith only [h10, h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h2, h4, h9, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h8, hc12, hlam, hphi, u2elo3]
                · linarith only [h7, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
                · rcases m.htr 1 2 4 (by decide) (by decide) with h17 | h17
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                      · linarith only [h16, h19, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h1, h18, h19, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h18, h2, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h17, hc12, hlam, hphi, u2elo3]
                · linarith only [h16, hc12, hlam, hphi, u2elo2]
            · linarith only [h4, h5, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h26 | h26
            · rcases m.htr 0 4 5 (by decide) (by decide) with h27 | h27
              · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
                · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
                    · linarith only [h1, h26, h30, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                      · linarith only [h26, h28, h32, h4, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h34 | h34
                        · linarith only [h0, h29, h34, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · linarith only [h27, h3, h32, h34, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h29, hc12, hlam, hphi, u2elo3]
                · linarith only [h28, hc12, hlam, hphi, u2elo2]
              · linarith only [h26, h27, h4, hc35, hlam, hphi, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h40 | h40
              · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
                · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                    · linarith only [h1, h4, h43, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
                      · linarith only [h4, h45, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
                        · linarith only [h0, h42, h47, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · linarith only [h3, h40, h47, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · linarith only [h42, hc12, hlam, hphi, u2elo3]
                · linarith only [h41, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
                · rcases m.htr 1 2 4 (by decide) (by decide) with h53 | h53
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h54 | h54
                    · linarith only [h1, h4, h54, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                      · linarith only [h0, h4, h52, h56, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h58 | h58
                        · linarith only [h0, h40, h53, h58, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h60 | h60
                          · rcases h3bigk with h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h4, h40, h52, h60, hc23, hc34, hlam, hphi, p61_1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h4, h40, hc23, hlam, hphi, ht34, ht45, p61_1, u5elo4]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h4, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h26, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h1, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h1, h4, h40, hc23, hlam, hphi, ht34, ht45, p61_1, u5elo4]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h54, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h1, h4, h40, h60, hlam, p61_1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h2, hlam, p61_1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h52, hlam, p61_1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h56, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h0, h4, h40, h53, h56, h60, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p61_1, u2elo0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              rcases p61_3 (m.d 0 3) (by simp) with h77 | h77
                              · linarith only [h77, hlam, p61_0]
                              · rcases p61_3 (m.d 1 3) (by simp) with h79 | h79
                                · linarith only [h54, h79, hlam]
                                · rcases p61_3 (m.d 2 3) (by simp) with h81 | h81
                                  · linarith only [h56, h81, hlam]
                                  · rcases p61_3 (m.d 3 4) (by simp) with h83 | h83
                                    · rcases p61_3 (m.d 3 5) (by simp) with h84 | h84
                                      · linarith only [h60, h84, hlam]
                                      · linarith only [h26, h84, hlam]
                                    · linarith only [h83, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              rcases p61_3 (m.d 0 3) (by simp) with h88 | h88
                              · linarith only [h4, h88, hlam]
                              · linarith only [h1, h88, hlam]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              rcases p61_3 (m.d 0 3) (by simp) with h91 | h91
                              · linarith only [h4, h91, hlam]
                              · linarith only [h2, h91, hlam]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h1, h4, h40, h52, h60, hc23, hc34, hlam, hphi, p61_1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h1, h52, hc23, hlam, hphi, ht34, ht45, p61_1, u5elo3]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h52, hc23, hlam, hphi, ht34, ht45, p61_1, u5elo3]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hc23, hlam, hphi, ht34, ht45, p61_1, u5elo3]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h60, hlam, p61_1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                          · linarith only [h1, h4, h52, h60, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h53, hc12, hlam, hphi, u2elo3]
                · linarith only [h52, hc12, hlam, hphi, u2elo2]
        · linarith only [h3, hc02, hlam, hphi, u2elo3]
      · linarith only [h0, h2, hc12, hlam, hphi, u2elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h106 | h106
      · linarith only [h0, h1, h106, hc12, hlam, hphi, u2elo0]
      · linarith only [h106, hc02, hlam, hphi, u2elo2]
  · linarith only [h0, hc01, hlam, hphi, ht12, u2elo1]

theorem r1l7_22_13_15_H_R_L_I_L_R (m : N7Model)
    (hb2 : CMSig2_7_H_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
      · linarith only [h2, hc23, hlam, hphi, u2ehi1]
    · linarith only [h1, hc23, hlam, hphi, u2ehi0]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6 | h6
    · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
      · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
        · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
            · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
              · linarith only [h11, h6, h8, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases h3bigk with h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [hlam, p13_0]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [h0, h10, h6, h7, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p13_1, u2ehi4]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [h0, h10, h6, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p13_1, u2ehi4]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  rcases p13_3 (m.d 0 3) (by simp) with h17 | h17
                  · rcases p13_3 (m.d 1 3) (by simp) with h18 | h18
                    · rcases p13_3 (m.d 2 3) (by simp) with h19 | h19
                      · linarith only [h19, h6, hlam]
                      · linarith only [h19, h8, hlam]
                    · linarith only [h10, h11, h18, h7, h8, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                  · linarith only [h17, hlam, p13_0]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  rcases p13_3 (m.d 0 3) (by simp) with h24 | h24
                  · rcases p13_3 (m.d 1 3) (by simp) with h25 | h25
                    · rcases p13_3 (m.d 2 3) (by simp) with h26 | h26
                      · linarith only [h26, h6, hlam]
                      · linarith only [h26, h9, hlam]
                    · linarith only [h10, h11, h25, h7, h8, hlam]
                  · linarith only [h24, hlam, p13_0]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [h10, h6, h8, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p13_1, u2ehi4]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [hlam, p13_0]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [h10, h7, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p13_1, u2ehi4]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  rcases p13_3 (m.d 0 3) (by simp) with h34 | h34
                  · rcases p13_3 (m.d 1 3) (by simp) with h35 | h35
                    · rcases p13_3 (m.d 2 3) (by simp) with h36 | h36
                      · linarith only [h36, h7, hlam]
                      · linarith only [h36, h8, hlam]
                    · linarith only [h35, hlam, p13_0]
                  · linarith only [h10, h11, h34, h6, h8, hlam]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  rcases p13_3 (m.d 0 3) (by simp) with h41 | h41
                  · rcases p13_3 (m.d 1 3) (by simp) with h42 | h42
                    · rcases p13_3 (m.d 2 3) (by simp) with h43 | h43
                      · linarith only [h43, h7, hlam]
                      · linarith only [h43, h9, hlam]
                    · linarith only [h42, hlam, p13_0]
                  · linarith only [h10, h11, h41, h6, h8, hlam]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [h6, hlam, p13_1]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [h7, hlam, p13_1]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [hlam, p13_0]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  rcases p13_3 (m.d 0 3) (by simp) with h51 | h51
                  · rcases p13_3 (m.d 1 3) (by simp) with h52 | h52
                    · rcases p13_3 (m.d 2 3) (by simp) with h53 | h53
                      · rcases p13_3 (m.d 3 4) (by simp) with h54 | h54
                        · linarith only [h54, hlam, p13_0]
                        · rcases p13_3 (m.d 3 5) (by simp) with h56 | h56
                          · linarith only [h56, h9, hlam]
                          · linarith only [h11, h56, hlam]
                      · linarith only [h53, hlam, p13_0]
                    · linarith only [h10, h11, h52, h7, h8, hlam]
                  · linarith only [h10, h11, h51, h6, h8, hlam]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [h0, h6, hc12, hlam, hphi, ht01, ht0b, ht5b, p13_1, u5ehi3]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [h10, h11, h6, h8, hlam, p13_1]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [h10, h11, h7, h8, hlam, p13_1]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [h8, hlam, p13_0]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [hlam, p13_0]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [h11, hlam, p13_0]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [h10, h6, h8, hc35, hlam, hphi, ht23, p13_1, u2ehi4]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [h10, h11, h7, h8, hlam, p13_1]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [h9, hlam, p13_0]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [h0, h10, h11, h6, h8, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13_1]
                · have p13_0 := h13c.1
                  have p13_1 := h13c.2.1
                  have p13_2 := h13c.2.2.1
                  have p13_3 := h13c.2.2.2
                  linarith only [hlam, p13_0]
            · linarith only [h10, hc45, hlam, hphi, ht23, ht34, u2ehi3]
          · linarith only [h9, hc35, hlam, hphi, ht23, u2ehi2]
        · linarith only [h8, hc34, hlam, hphi, ht23, u2ehi2]
      · linarith only [h0, h7, hc23, hlam, hphi, u2ehi0]
    · linarith only [h6, hc23, hlam, hphi, u2ehi0]

theorem r1l7_22_13_15_M_IR_L_0_L_0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h4, h6, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h4, h6, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h8, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                · linarith only [h7, hlam, hphi, ht23, u2ehi2, u3elo4]
              · linarith only [h6, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
          · linarith only [h4, hlam, hphi, ht23, u2ehi1, u3elo2]
        · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · linarith only [h0, h2, hlam, hphi, ht23, u2ehi1, u3elo2]
    · linarith only [h0, h1, hlam, hphi, ht23, u2ehi1, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h20 | h20
    · rcases m.htr 0 2 3 (by decide) (by decide) with h21 | h21
      · rcases m.htr 0 2 5 (by decide) (by decide) with h22 | h22
        · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
          · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
            · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
              · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                · rcases m.htr 2 4 5 (by decide) (by decide) with h27 | h27
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                    · linarith only [h0, h20, h23, h25, h28, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h20, h23, h25, h27, h28, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h27, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                · linarith only [h26, hlam, hphi, ht23, u2ehi2, u3elo4]
              · linarith only [h25, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h0, h21, h24, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h20, h21, h23, hlam]
        · linarith only [h21, h22, hc25, hlam, hphi, u2ehi2]
      · linarith only [h21, hlam, hphi, ht23, u2ehi0, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h38 | h38
      · rcases m.htr 0 2 5 (by decide) (by decide) with h39 | h39
        · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
          · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
            · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
              · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h45 | h45
                    · rcases h2bigk with h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [hlam, p46_0]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [h0, hlam, p46_0]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [h0, h42, h45, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p46_1]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        rcases p46_3 (m.d 0 2) (by simp) with h50 | h50
                        · rcases p46_3 (m.d 1 2) (by simp) with h51 | h51
                          · rcases p46_3 (m.d 2 3) (by simp) with h52 | h52
                            · linarith only [h38, h52, hlam]
                            · linarith only [h42, h52, hlam]
                          · linarith only [h41, h51, hlam]
                        · linarith only [h50, hlam, p46_0]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        rcases p46_3 (m.d 0 2) (by simp) with h57 | h57
                        · rcases p46_3 (m.d 1 2) (by simp) with h58 | h58
                          · rcases p46_3 (m.d 2 3) (by simp) with h59 | h59
                            · linarith only [h38, h59, hlam]
                            · linarith only [h43, h59, hlam]
                          · linarith only [h0, h38, h42, h45, h58, hc45, hlam, hphi, u5elo2]
                        · linarith only [h57, hlam, p46_0]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [h38, h42, h45, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p46_1]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [hlam, p46_0]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [h42, h45, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p46_1]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        rcases p46_3 (m.d 0 2) (by simp) with h67 | h67
                        · linarith only [h0, h67, hlam]
                        · linarith only [h38, h42, h45, h67, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p46_1]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        rcases p46_3 (m.d 0 2) (by simp) with h70 | h70
                        · linarith only [h0, h70, hlam]
                        · linarith only [h39, h70, hlam]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [h38, hlam, p46_0]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [h40, hlam, p46_0]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [hlam, p46_0]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [h20, h38, hlam, hphi, ht23, p46_1, u2ehi3, u3elo1]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [h20, h38, hlam, hphi, ht23, p46_1, u2ehi4, u3elo1]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [h38, h42, h45, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p46_1]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [h41, hlam, p46_0]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [h42, hlam, p46_0]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [hlam, p46_0]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [h20, h38, h42, hlam, hphi, ht23, p46_1, u2ehi4, u3elo1]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [h39, hlam, p46_0]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [hc25, hlam, hphi, p46_1, u2ehi1]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [h43, hlam, p46_0]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [h44, hlam, p46_1]
                      · have p46_0 := h46c.1
                        have p46_1 := h46c.2.1
                        have p46_2 := h46c.2.2.1
                        have p46_3 := h46c.2.2.2
                        linarith only [hlam, p46_0]
                    · rcases h2bigk with h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h0, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h0, h42, h44, h45, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p88_1]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h0, h44, h45, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p88_1]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        rcases p88_3 (m.d 0 2) (by simp) with h93 | h93
                        · rcases p88_3 (m.d 1 2) (by simp) with h94 | h94
                          · rcases p88_3 (m.d 2 3) (by simp) with h95 | h95
                            · linarith only [h38, h95, hlam]
                            · linarith only [h43, h95, hlam]
                          · linarith only [h0, h94, hlam, p88_1]
                        · linarith only [h93, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h38, h42, h44, h45, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p88_1]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h42, h44, h45, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p88_1]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h44, h45, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p88_1]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        rcases p88_3 (m.d 0 2) (by simp) with h104 | h104
                        · linarith only [h0, h104, hlam]
                        · linarith only [h104, h39, hlam]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h38, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h40, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h20, h38, h44, h45, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p88_1, u3elo1]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h20, h38, hlam, hphi, ht23, p88_1, u2ehi4, u3elo1]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [hc24, hlam, hphi, p88_1, u2ehi0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h41, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h42, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h20, h38, h42, hlam, hphi, ht23, p88_1, u2ehi4, u3elo1]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h39, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h0, hc25, hlam, hphi, p88_1, u2ehi0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h43, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h44, hlam, p88_1]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [hlam, p88_0]
                  · linarith only [h44, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                · linarith only [h43, hlam, hphi, ht23, u2ehi2, u3elo4]
              · linarith only [h42, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h0, h38, h41, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h38, h40, hlam]
        · linarith only [h38, h39, hc25, hlam, hphi, u2ehi2]
      · linarith only [h38, hlam, hphi, ht23, u2ehi0, u3elo2]

theorem r1l7_22_13_15_M_IR_L_0_L_R (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h6, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h8, hlam, hphi, ht23, u2ehi2, u3elo4]
                · linarith only [h7, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h6, hlam, hphi, ht23, u2ehi1, u3elo2]
            · linarith only [h2, h5, hlam, hphi, ht23, u2ehi2, u3elo4]
          · linarith only [h2, h4, hc25, hlam, hphi, u2ehi2]
        · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
      · linarith only [h2, hlam, hphi, ht23, u2ehi0, u3elo2]
    · linarith only [h0, h1, hlam, hphi, ht23, u2ehi1, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h18 | h18
    · rcases m.htr 0 2 3 (by decide) (by decide) with h19 | h19
      · rcases m.htr 0 2 4 (by decide) (by decide) with h20 | h20
        · rcases m.htr 0 2 5 (by decide) (by decide) with h21 | h21
          · rcases m.htr 0 3 5 (by decide) (by decide) with h22 | h22
            · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
              · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                  · linarith only [h0, h18, h23, h25, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h24, h25, hlam, hphi, ht23, u2ehi3, u3elo4]
                · linarith only [h24, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h0, h23, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h19, h22, hlam, hphi, ht23, u2ehi2, u3elo4]
          · linarith only [h19, h21, hc25, hlam, hphi, u2ehi2]
        · linarith only [h19, h20, hc24, hlam, hphi, u2ehi2]
      · linarith only [h19, hlam, hphi, ht23, u2ehi0, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h34 | h34
      · rcases m.htr 0 2 4 (by decide) (by decide) with h35 | h35
        · rcases m.htr 0 2 5 (by decide) (by decide) with h36 | h36
          · rcases m.htr 0 3 5 (by decide) (by decide) with h37 | h37
            · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
              · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                · rcases m.htr 2 3 5 (by decide) (by decide) with h40 | h40
                  · rcases h2bigk with h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [hlam, p41_0]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [h0, hlam, p41_0]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [h0, h40, hc12, hlam, hphi, ht01, ht0b, ht5b, p41_1, u5ehi3]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      rcases p41_3 (m.d 0 2) (by simp) with h45 | h45
                      · rcases p41_3 (m.d 1 2) (by simp) with h46 | h46
                        · rcases p41_3 (m.d 2 3) (by simp) with h47 | h47
                          · linarith only [h34, h47, hlam]
                          · linarith only [h39, h47, hlam]
                        · linarith only [h0, h46, hlam, p41_1]
                      · linarith only [h45, hlam, p41_0]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      rcases p41_3 (m.d 0 2) (by simp) with h52 | h52
                      · rcases p41_3 (m.d 1 2) (by simp) with h53 | h53
                        · rcases p41_3 (m.d 2 3) (by simp) with h54 | h54
                          · linarith only [h34, h54, hlam]
                          · linarith only [h40, h54, hlam]
                        · linarith only [h0, h53, hlam, p41_1]
                      · linarith only [h52, hlam, p41_0]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [h34, h40, hc12, hlam, hphi, ht01, ht0b, ht5b, p41_1, u5ehi3]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [hlam, p41_0]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [h40, hc12, hlam, hphi, ht01, ht0b, ht5b, p41_1, u5ehi3]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      rcases p41_3 (m.d 0 2) (by simp) with h62 | h62
                      · linarith only [h0, h62, hlam]
                      · linarith only [h35, h62, hlam]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      rcases p41_3 (m.d 0 2) (by simp) with h65 | h65
                      · linarith only [h0, h65, hlam]
                      · linarith only [h36, h65, hlam]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [h34, hlam, p41_0]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [h38, hlam, p41_0]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [hlam, p41_0]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [h18, h34, hlam, hphi, ht23, p41_1, u2ehi3, u3elo1]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [h18, h34, hlam, hphi, ht23, p41_1, u2ehi4, u3elo1]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [h35, hlam, p41_0]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [hc24, hlam, hphi, p41_1, u2ehi1]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [h39, hlam, p41_0]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [hlam, p41_0]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [h18, h34, h39, hlam, hphi, ht23, p41_1, u2ehi4, u3elo1]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [h36, hlam, p41_0]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [h0, h34, h40, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p41_1, u5ehi3]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [h40, hlam, p41_0]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [h18, h36, h37, hlam, hphi, ht23, p41_1, u2ehi3, u3elo1]
                    · have p41_0 := h41c.1
                      have p41_1 := h41c.2.1
                      have p41_2 := h41c.2.2.1
                      have p41_3 := h41c.2.2.2
                      linarith only [hlam, p41_0]
                  · linarith only [h40, hlam, hphi, ht23, u2ehi2, u3elo4]
                · linarith only [h39, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h0, h34, h38, hlam]
            · linarith only [h34, h37, hlam, hphi, ht23, u2ehi2, u3elo4]
          · linarith only [h34, h36, hc25, hlam, hphi, u2ehi2]
        · linarith only [h34, h35, hc24, hlam, hphi, u2ehi2]
      · linarith only [h34, hlam, hphi, ht23, u2ehi0, u3elo2]

theorem r1l7_22_13_15_M_IR_L_R_L_0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h4, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h6, h7, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                · linarith only [h12, h6, hc34, hlam, hphi, u3ehi4]
                · linarith only [h12, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
            · linarith only [h3, h5, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
            · linarith only [h16, h4, hc23, hlam, hphi, u2ehi4]
            · linarith only [h16, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
        · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · linarith only [h1, h2, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h21 | h21
      · linarith only [h1, h21, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h23 | h23
        · linarith only [h1, h23, hc23, hlam, hphi, u2ehi4]
        · linarith only [h23, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h26 | h26
    · rcases m.htr 0 2 4 (by decide) (by decide) with h27 | h27
      · rcases m.htr 0 2 5 (by decide) (by decide) with h28 | h28
        · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
          · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
            · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
              · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
                · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
                        · rcases h2bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [hlam, p37_0]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [h0, hlam, p37_0]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [h33, h36, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1, u3ehi4]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            rcases p37_3 (m.d 0 2) (by simp) with h41 | h41
                            · rcases p37_3 (m.d 1 2) (by simp) with h42 | h42
                              · rcases p37_3 (m.d 2 3) (by simp) with h43 | h43
                                · linarith only [h26, h43, hlam]
                                · linarith only [h33, h43, hlam]
                              · linarith only [h0, h42, hlam, p37_1]
                            · linarith only [h41, hlam, p37_0]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            rcases p37_3 (m.d 0 2) (by simp) with h48 | h48
                            · rcases p37_3 (m.d 1 2) (by simp) with h49 | h49
                              · rcases p37_3 (m.d 2 3) (by simp) with h50 | h50
                                · linarith only [h26, h50, hlam]
                                · linarith only [h34, h50, hlam]
                              · linarith only [h30, h49, hlam]
                            · linarith only [h48, hlam, p37_0]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [h26, h33, h36, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p37_1, u3ehi4]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [hlam, p37_0]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [h33, h36, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p37_1, u3ehi4]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            rcases p37_3 (m.d 0 2) (by simp) with h58 | h58
                            · linarith only [h0, h58, hlam]
                            · linarith only [h27, h58, hlam]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            rcases p37_3 (m.d 0 2) (by simp) with h61 | h61
                            · linarith only [h0, h61, hlam]
                            · linarith only [h28, h61, hlam]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [h26, hlam, p37_0]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [h29, hlam, p37_0]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [hlam, p37_0]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [h26, h35, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p37_1, u2ehi4]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [h0, h26, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p37_1, u2ehi4]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [h27, hlam, p37_0]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [h0, h26, h27, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1, u3ehi2]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [h33, hlam, p37_0]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [hlam, p37_0]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [h0, h26, h33, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p37_1, u2ehi4]
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
                            linarith only [h34, hlam, p37_0]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [h35, hlam, p37_1]
                          · have p37_0 := h37c.1
                            have p37_1 := h37c.2.1
                            have p37_2 := h37c.2.2.1
                            have p37_3 := h37c.2.2.2
                            linarith only [hlam, p37_0]
                        · linarith only [h36, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                      · linarith only [h35, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                    · linarith only [h34, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                    · linarith only [h31, h33, h82, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h82, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · linarith only [h32, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h86 | h86
                · linarith only [h31, h86, hc34, hlam, hphi, u3ehi4]
                · linarith only [h86, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
            · linarith only [h0, h30, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
          · linarith only [h0, h26, h29, hlam]
        · linarith only [h26, h28, hc25, hlam, hphi, u2ehi2]
      · linarith only [h26, h27, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h93 | h93
      · linarith only [h26, h93, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h95 | h95
        · linarith only [h26, h95, hc23, hlam, hphi, u2ehi4]
        · linarith only [h95, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem r1l7_22_13_15_M_LI_L_R_L_0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                · linarith only [h2, h5, h7, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
              · linarith only [h6, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
              · linarith only [h11, h5, hc34, hlam, hphi, u3ehi4]
              · linarith only [h11, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
          · linarith only [h2, h4, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
        · linarith only [h1, h2, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
      · linarith only [h0, h2, hc12, hlam, hphi, u2elo0]
    · linarith only [h0, h1, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h18 | h18
    · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
      · linarith only [h0, h19, hc02, hlam, hphi, u2elo1]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
        · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
          · rcases m.htr 1 3 4 (by decide) (by decide) with h23 | h23
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24 | h24
              · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                · linarith only [h0, h18, h25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                · linarith only [h0, h21, h23, h25, hc02, hlam, hphi, u2elo1]
              · linarith only [h23, h24, hlam, hphi, ht34, ht45, u3ehi3, u5elo3]
            · linarith only [h19, h21, h23, hlam]
          · linarith only [h21, h22, hc24, hlam, hphi, ht45, u5elo2]
        · linarith only [h18, h21, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
      · linarith only [h0, h32, hc02, hlam, hphi, u2elo1]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
        · linarith only [h18, h32, h34, hc02, hlam, hphi, u2elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
          · rcases m.htr 1 3 4 (by decide) (by decide) with h37 | h37
            · rcases m.htr 1 3 5 (by decide) (by decide) with h38 | h38
              · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                · rcases m.htr 2 3 5 (by decide) (by decide) with h40 | h40
                  · linarith only [h34, h36, h39, h40, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
                  · linarith only [h34, h38, h39, h40, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
                · linarith only [h32, h36, h37, h38, h39, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
              · linarith only [h38, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h45 | h45
              · linarith only [h37, h45, hc34, hlam, hphi, u3ehi4]
              · linarith only [h45, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
            · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
              · rcases m.htr 2 3 4 (by decide) (by decide) with h50 | h50
                · rcases m.htr 2 3 5 (by decide) (by decide) with h51 | h51
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h52 | h52
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h53 | h53
                      · rcases h2bigk with h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [hlam, p54_0]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [hc12, hlam, hphi, p54_1, u2elo0]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [h0, hlam, p54_0]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [h18, hlam, p54_0]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [h18, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p54_1, u2elo3]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [h36, hc02, hlam, hphi, p54_1, u2elo4]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [hlam, p54_0]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [h32, hlam, p54_0]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [h34, hlam, p54_0]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [h36, hlam, p54_0]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [hc02, hlam, hphi, p54_1, u2elo2]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [hc12, hlam, hphi, p54_1, u2elo2]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [hlam, p54_0]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [h18, hc02, hlam, hphi, p54_1, u2elo2]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [h36, hc12, hlam, hphi, p54_1, u2elo2]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [hc02, hlam, hphi, p54_1, u2elo3]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [hc12, hlam, hphi, p54_1, u2elo3]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [h50, hlam, p54_0]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [hlam, p54_0]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [h36, h50, hc12, hlam, hphi, p54_1, u2elo2]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [hc02, hlam, hphi, p54_1, u2elo4]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [hc12, hlam, hphi, p54_1, u2elo4]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [h51, hlam, p54_0]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [h52, hlam, p54_1]
                        · have p54_0 := h54c.1
                          have p54_1 := h54c.2.1
                          have p54_2 := h54c.2.2.1
                          have p54_3 := h54c.2.2.2
                          linarith only [hlam, p54_0]
                      · linarith only [h53, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h18, h52, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h32, h48, h51, hc35, hlam, hphi, u3ehi3]
                · linarith only [h32, h48, h50, hlam]
              · linarith only [h48, h49, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h85 | h85
              · linarith only [h48, h85, hc34, hlam, hphi, u3ehi4]
              · linarith only [h85, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]

theorem r1l7_22_14_M_IR_L_0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h4elo := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h3, h6, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h3, h6, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h7, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
              · linarith only [h6, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
            · linarith only [h3, h5, hc25, hlam, hphi, u2ehi2]
          · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
          · linarith only [h15, h3, hc23, hlam, hphi, u2ehi3]
          · linarith only [h15, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
      · linarith only [h1, h2, hc25, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h19 | h19
      · linarith only [h1, h19, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h21 | h21
        · linarith only [h0, h1, h21, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
          · linarith only [h0, h1, h23, hc23, hlam, hphi, u2ehi3]
          · linarith only [h23, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h26 | h26
    · rcases m.htr 0 2 5 (by decide) (by decide) with h27 | h27
      · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
        · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
          · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
            · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
              · rcases m.htr 2 4 5 (by decide) (by decide) with h32 | h32
                · rcases m.htr 3 4 5 (by decide) (by decide) with h33 | h33
                  · rcases h2bigk with h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [hlam, p34_0]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [h0, hlam, p34_1]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [h31, h33, hc02, hc45, hlam, hphi, ht0b, ht5b, p34_1]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      rcases p34_3 (m.d 0 2) (by simp) with h38 | h38
                      · rcases p34_3 (m.d 1 2) (by simp) with h39 | h39
                        · rcases p34_3 (m.d 2 3) (by simp) with h40 | h40
                          · linarith only [h26, h40, hlam]
                          · linarith only [h31, h40, hlam]
                        · linarith only [h29, h39, hlam]
                      · linarith only [h38, hlam, p34_0]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      rcases p34_3 (m.d 0 2) (by simp) with h45 | h45
                      · rcases p34_3 (m.d 1 2) (by simp) with h46 | h46
                        · rcases p34_3 (m.d 2 3) (by simp) with h47 | h47
                          · linarith only [h26, h47, hlam]
                          · linarith only [h0, h31, h33, h47, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p34_1]
                        · linarith only [h30, h46, hlam]
                      · linarith only [h45, hlam, p34_0]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [h26, h31, h33, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p34_1]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [hlam, p34_0]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [h31, h33, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p34_1]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      rcases p34_3 (m.d 0 2) (by simp) with h55 | h55
                      · linarith only [h0, h55, hlam]
                      · linarith only [h26, h31, h33, h55, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p34_1]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      rcases p34_3 (m.d 0 2) (by simp) with h58 | h58
                      · linarith only [h0, h58, hlam]
                      · linarith only [h27, h58, hlam]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [h26, hlam, p34_0]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [h28, hlam, p34_0]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [hlam, p34_0]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [h26, h32, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p34_1, u2ehi4]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [h0, h26, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p34_1, u2ehi4]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [hc24, hlam, hphi, p34_1, u2ehi0]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [h29, hlam, p34_0]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [h31, hlam, p34_1]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [hlam, p34_0]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [h29, hlam, hphi, ht23, ht34, p34_1, u2ehi4, u4elo1]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [h27, hlam, p34_0]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [h30, hlam, p34_0]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [h31, h33, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p34_1]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [h32, hlam, p34_0]
                    · have p34_0 := h34c.1
                      have p34_1 := h34c.2.1
                      have p34_2 := h34c.2.2.1
                      have p34_3 := h34c.2.2.2
                      linarith only [hlam, p34_0]
                  · linarith only [h29, h32, h33, hc34, hlam, hphi, u4elo1]
                · linarith only [h32, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
              · linarith only [h31, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
            · linarith only [h0, h27, h30, hlam]
          · linarith only [h0, h26, h29, hc24, hlam, hphi, u2ehi2]
        · linarith only [h0, h26, h28, hlam]
      · linarith only [h26, h27, hc25, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h83 | h83
      · linarith only [h26, h83, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
        · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
          · rcases m.htr 1 2 5 (by decide) (by decide) with h87 | h87
            · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
              · rcases m.htr 2 4 5 (by decide) (by decide) with h89 | h89
                · linarith only [h83, h86, h89, hlam, hphi, ht23, ht34, u2ehi0, u4elo1]
                · linarith only [h89, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
              · linarith only [h88, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
            · linarith only [h26, h85, h87, hc25, hlam, hphi, u2ehi0]
          · linarith only [h26, h85, h86, hc24, hlam, hphi, u2ehi0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
          · linarith only [h85, h95, hc23, hlam, hphi, u2ehi3]
          · linarith only [h95, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]

end R2N4
