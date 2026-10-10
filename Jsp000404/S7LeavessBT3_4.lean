import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sBT3_H_I_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h3elo := hb3.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h14, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h14, h6, hc23, hlam, hphi, u3elo0]
                            · linarith only [h13, h5, hc23, hlam, hphi, u3elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                              · linarith only [h0, h19, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h19, h6, hc23, hlam, hphi, u3elo0]
                            · linarith only [h18, h5, hc23, hlam, hphi, u3elo0]
                        · linarith only [h11, h6, hc13, hlam, hphi, u3elo0]
                      · linarith only [h10, h4, h5, h7, h8, hc23, hlam, hphi, u3elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h26 | h26
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h27 | h27
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                            · linarith only [h26, h28, h8, h9, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi3]
                            · linarith only [h28, h5, hc23, hlam, hphi, u3elo0]
                          · linarith only [h26, h27, h5, h7, h8, h9, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
                        · linarith only [h26, h6, hc13, hlam, hphi, u3elo0]
                      · linarith only [h25, h4, h5, h7, h8, hc23, hlam, hphi, u3elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h35 | h35
                      · linarith only [h35, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h37 | h37
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h38 | h38
                          · linarith only [h34, h35, h38, h4, h5, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h41 | h41
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
                                · linarith only [h34, h35, h38, h4, h42, h5, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi1]
                                · linarith only [h35, h42, h5, h7, hc12, hlam, hphi, ht23, u3elo0]
                              · linarith only [h37, h41, hc23, hlam, hphi, u3elo1]
                            · linarith only [h40, h5, h8, hc13, hlam, hphi, u3elo0]
                        · linarith only [h37, h6, h8, hc12, hlam, hphi, ht23, u3elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
                      · linarith only [h48, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h50 | h50
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h51 | h51
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h53 | h53
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h54 | h54
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h55 | h55
                                  · linarith only [h3, h52, h55, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                                  · rcases h5bigk with h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [hlam, p57_0]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h48, h5, h7, hc12, hlam, hphi, ht23, p57_1, u3elo0]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h5, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p57_1, u3elo0, u5ehi2]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h5, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p57_1, u3elo0, u5ehi3]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h5, h55, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p57_1, u3elo0]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h2, hlam, p57_0]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [hlam, p57_0]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h48, hlam, p57_0]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p57_1, u5ehi3]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h4, h48, h5, h55, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p57_1, u3elo0]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h4, hlam, p57_1]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h4, h5, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p57_1, u3elo0, u5ehi1]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [hlam, p57_0]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h4, h5, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p57_1, u3elo0, u5ehi3]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h4, h5, h55, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p57_1, u3elo0]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h6, hlam, p57_1]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h50, hlam, p57_1]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h53, hlam, p57_0]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [hlam, p57_0]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h55, hlam, p57_1]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h7, hlam, p57_0]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h51, hlam, p57_0]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h54, hlam, p57_0]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [h51, hc14, hlam, hphi, ht01, ht0b, ht5b, p57_1, u5ehi3]
                                    · have p57_0 := h57c.1
                                      have p57_1 := h57c.2.1
                                      have p57_2 := h57c.2.2.1
                                      have p57_3 := h57c.2.2.2
                                      linarith only [hlam, p57_0]
                                · linarith only [h34, h51, h54, hlam]
                              · linarith only [h34, h51, h52, h53, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                            · linarith only [h50, h52, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                          · linarith only [h34, h5, h51, h7, hc12, hlam, hphi, ht23, u3elo0]
                        · linarith only [h50, h6, hc13, hlam, hphi, u3elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h89 | h89
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h90 | h90
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h91 | h91
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
                          · linarith only [h2, h7, h92, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
                              · linarith only [h0, h88, h95, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h91, h95, hc23, hlam, hphi, u3elo1]
                            · linarith only [h5, h94, hc23, hlam, hphi, u3elo0]
                        · linarith only [h6, h91, hc13, hlam, hphi, u3elo0]
                      · linarith only [h4, h6, h88, h90, hc23, hlam, hphi, u3elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h102 | h102
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h103 | h103
                          · linarith only [h103, h2, h7, hlam]
                          · linarith only [h102, h103, h88, h89, hlam]
                        · linarith only [h102, h6, hc13, hlam, hphi, u3elo0]
                      · linarith only [h101, h4, h6, h88, hc23, hlam, hphi, u3elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h108 | h108
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h109 | h109
                      · linarith only [h109, h88, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h111 | h111
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h112 | h112
                          · linarith only [h108, h109, h112, h4, h6, h7, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h114 | h114
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h115 | h115
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h116 | h116
                                · linarith only [h108, h109, h116, h4, h7, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h118 | h118
                                  · linarith only [h109, h118, h4, h7, hc12, hlam, hphi, ht23, u3elo3]
                                  · rcases h5bigk with h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [hlam, p120_0]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p120_1, u3elo0, u5ehi1]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h108, h109, h114, h7, hc34, hc45, hlam, hphi, p120_1]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p120_1, u3elo0, u5ehi3]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h7, hlam, p120_1]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h2, hlam, p120_0]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [hlam, p120_0]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h109, hlam, p120_0]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p120_1, u5ehi3]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h112, hlam, p120_1]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h4, hlam, p120_1]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p120_1, u5ehi1]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [hlam, p120_0]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h4, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p120_1, u3elo0, u5ehi3]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h116, hlam, p120_1]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h6, hlam, p120_1]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h111, hlam, p120_1]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h115, hlam, p120_0]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [hlam, p120_0]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h118, hlam, p120_1]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h108, h109, h114, h2, hc34, hc45, hlam, hphi, p120_1]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h108, h109, h114, hc34, hc45, hlam, hphi, p120_1]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [h108, h109, h114, hc34, hc45, hlam, hphi, p120_1]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      rcases p120_3 (m.d 0 5) (by simp) with h144 | h144
                                      · linarith only [h144, h7, hlam]
                                      · linarith only [h144, h6, hlam]
                                    · have p120_0 := h120c.1
                                      have p120_1 := h120c.2.1
                                      have p120_2 := h120c.2.2.1
                                      have p120_3 := h120c.2.2.2
                                      linarith only [hlam, p120_0]
                              · linarith only [h111, h115, hc23, hlam, hphi, u3elo1]
                            · linarith only [h111, h114, h88, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                        · linarith only [h111, h6, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h151 | h151
                      · linarith only [h151, h88, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h153 | h153
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h154 | h154
                          · linarith only [h154, h2, h7, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h156 | h156
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h157 | h157
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h158 | h158
                                · linarith only [h151, h156, h158, h3, h4, h7, hc12, hlam, hphi, ht23, u3elo0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h160 | h160
                                  · linarith only [h108, h156, h158, h160, h3, hc12, hlam, hphi, ht23, u3elo0]
                                  · rcases h5bigk with h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [hlam, p162_0]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p162_1, u3elo0, u5ehi1]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h151, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p162_1, u3elo0, u5ehi1]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p162_1, u3elo0, u5ehi3]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h7, hlam, p162_1]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h2, hlam, p162_0]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [hlam, p162_0]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h151, hlam, p162_0]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p162_1, u5ehi3]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h154, hlam, p162_1]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h4, hlam, p162_1]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p162_1, u5ehi1]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [hlam, p162_0]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h4, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p162_1, u3elo0, u5ehi3]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h158, hlam, p162_1]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h6, hlam, p162_1]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h153, hlam, p162_1]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h157, hlam, p162_0]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [hlam, p162_0]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h160, hlam, p162_1]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h151, h4, hc12, hc45, hlam, hphi, ht23, ht34, p162_1]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      rcases p162_3 (m.d 0 5) (by simp) with h184 | h184
                                      · linarith only [h184, h7, hlam]
                                      · linarith only [h184, h2, hlam]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [h108, h158, hc12, hc45, hlam, hphi, ht23, ht34, p162_1]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      rcases p162_3 (m.d 0 5) (by simp) with h188 | h188
                                      · linarith only [h188, h7, hlam]
                                      · linarith only [h188, h6, hlam]
                                    · have p162_0 := h162c.1
                                      have p162_1 := h162c.2.1
                                      have p162_2 := h162c.2.2.1
                                      have p162_3 := h162c.2.2.2
                                      linarith only [hlam, p162_0]
                              · linarith only [h153, h157, hc23, hlam, hphi, u3elo1]
                            · linarith only [h153, h156, h88, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                        · linarith only [h153, h6, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h195 | h195
                · linarith only [h195, h5, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h197 | h197
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h198 | h198
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h199 | h199
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h200 | h200
                        · linarith only [h1, h200, h6, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h202 | h202
                          · linarith only [h195, h2, h202, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h204 | h204
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h205 | h205
                              · linarith only [h1, h197, h205, h6, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h207 | h207
                                · linarith only [h198, h202, h207, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h209 | h209
                                  · linarith only [h1, h195, h197, h204, h209, h6, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                  · rcases h5bigk with h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h200, h6, hc13, hlam, hphi, p211_1, u3elo4]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p211_1, u3elo4, u5ehi2]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h6, hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h195, hlam, p211_1]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h2, hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p211_1, u5ehi2]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h200, hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h202, hlam, p211_1]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h4, hlam, p211_1]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h199, hlam, p211_1]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h205, hlam, p211_1]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h207, hlam, p211_1]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p211_1, u3elo4, u5ehi0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h199, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p211_1, u3elo4, u5ehi2]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p211_1, u3elo4, u5ehi2]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h209, hlam, p211_1]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h1, h197, h204, h6, hc34, hc45, hlam, hphi, p211_1]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h197, h200, h204, hc34, hc45, hlam, hphi, p211_1]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h204, h205, hc34, hc45, hlam, hphi, p211_1]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h1, h197, h204, h6, hc34, hc45, hlam, hphi, p211_1]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [hlam, p211_0]
                            · linarith only [h204, h5, h6, hc23, hlam, hphi, u3elo4]
                      · linarith only [h197, h199, h4, h6, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h239 | h239
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h240 | h240
                        · linarith only [h1, h240, h6, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h242 | h242
                          · linarith only [h195, h2, h242, hlam]
                          · linarith only [h198, h239, h242, hlam]
                      · linarith only [h197, h239, h4, h6, hc23, hlam, hphi, u3elo4]
                  · linarith only [h197, h3, h6, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h247 | h247
              · linarith only [h247, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h249 | h249
                · rcases m.htr 1 2 3 (by decide) (by decide) with h250 | h250
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h251 | h251
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h252 | h252
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h253 | h253
                        · linarith only [h1, h247, h253, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h255 | h255
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h256 | h256
                            · linarith only [h1, h250, h256, h5, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h258 | h258
                              · linarith only [h1, h247, h250, h258, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h260 | h260
                                · linarith only [h0, h251, h260, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · linarith only [h249, h256, h260, h5, hc23, hlam, hphi, u3elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h263 | h263
                            · linarith only [h249, h251, h255, h263, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · linarith only [h249, h251, h255, h263, h5, hc23, hlam, hphi, u3elo3]
                      · linarith only [h249, h250, h252, h4, h5, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h267 | h267
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h268 | h268
                        · linarith only [h1, h247, h268, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h270 | h270
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h271 | h271
                            · linarith only [h271, h5, hc03, hlam, hphi, u3elo2]
                            · linarith only [h251, h267, h271, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi2]
                          · linarith only [h249, h251, h267, h270, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · linarith only [h249, h250, h267, h4, h5, hc23, hlam, hphi, u3elo3]
                  · linarith only [h250, h3, h5, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h277 | h277
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h278 | h278
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h279 | h279
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h280 | h280
                        · linarith only [h1, h280, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h282 | h282
                          · linarith only [h2, h249, h282, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h284 | h284
                            · linarith only [h1, h277, h284, h5, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h286 | h286
                              · linarith only [h1, h277, h286, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h288 | h288
                                · linarith only [h278, h282, h288, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h290 | h290
                                  · linarith only [h249, h290, h5, hc03, hlam, hphi, u3elo3]
                                  · rcases h5bigk with h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [hlam, p292_0]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [h247, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p292_1, u3elo4, u5ehi1]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [h247, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p292_1, u3elo4, u5ehi2]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [h247, hlam, p292_0]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [h249, hlam, p292_1]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [h2, hlam, p292_0]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [hlam, p292_0]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p292_1, u5ehi2]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [h280, hlam, p292_0]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [h282, hlam, p292_1]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [h4, hlam, p292_1]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [h279, hlam, p292_1]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [hlam, p292_0]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [h286, hlam, p292_1]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [h288, hlam, p292_1]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p292_1, u3elo4, u5ehi0]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [h279, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p292_1, u3elo4, u5ehi2]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p292_1, u3elo4, u5ehi2]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [hlam, p292_0]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [h290, hlam, p292_1]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      rcases p292_3 (m.d 0 5) (by simp) with h313 | h313
                                      · linarith only [h249, h313, hlam]
                                      · rcases p292_3 (m.d 1 5) (by simp) with h315 | h315
                                        · linarith only [h282, h315, hlam]
                                        · rcases p292_3 (m.d 2 5) (by simp) with h317 | h317
                                          · linarith only [h288, h317, hlam]
                                          · rcases p292_3 (m.d 3 5) (by simp) with h319 | h319
                                            · linarith only [h290, h319, hlam]
                                            · linarith only [h247, h319, hlam]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      rcases p292_3 (m.d 0 5) (by simp) with h322 | h322
                                      · linarith only [h249, h322, hlam]
                                      · linarith only [h2, h322, hlam]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      rcases p292_3 (m.d 0 5) (by simp) with h325 | h325
                                      · linarith only [h249, h325, hlam]
                                      · linarith only [h325, h4, hlam]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [h1, h247, h277, hc23, hc45, hlam, hphi, ht34, p292_1]
                                    · have p292_0 := h292c.1
                                      have p292_1 := h292c.2.1
                                      have p292_2 := h292c.2.2.1
                                      have p292_3 := h292c.2.2.2
                                      linarith only [hlam, p292_0]
                      · linarith only [h247, h277, h279, h4, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h331 | h331
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h332 | h332
                        · linarith only [h1, h2, h247, h332, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h334 | h334
                          · linarith only [h2, h249, h334, hlam]
                          · linarith only [h278, h331, h334, hlam]
                      · linarith only [h247, h277, h331, h4, hc23, hlam, hphi, u3elo4]
                  · linarith only [h277, h3, h5, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h339 | h339
            · rcases m.htr 0 3 5 (by decide) (by decide) with h340 | h340
              · linarith only [h3, h340, h4, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h342 | h342
                · linarith only [h339, h340, h342, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h344 | h344
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h345 | h345
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h346 | h346
                      · linarith only [h0, h346, h4, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h348 | h348
                        · linarith only [h1, h340, h348, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h350 | h350
                          · linarith only [h0, h342, h345, h350, h4, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h352 | h352
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h353 | h353
                              · linarith only [h340, h353, hc03, hlam, hphi, u3elo2]
                              · linarith only [h3, h352, h353, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                            · linarith only [h339, h352, hc23, hlam, hphi, u3elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h357 | h357
                      · linarith only [h0, h357, h4, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h359 | h359
                        · linarith only [h340, h359, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h361 | h361
                          · linarith only [h2, h342, h361, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h363 | h363
                            · linarith only [h344, h345, h361, h363, hc34, hc45, hlam, hphi]
                            · linarith only [h339, h363, hc23, hlam, hphi, u3elo0]
                  · linarith only [h3, h340, h344, h4, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h367 | h367
              · linarith only [h339, h367, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h369 | h369
                · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h371 | h371
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h372 | h372
                      · linarith only [h0, h372, h4, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
                        · linarith only [h367, h374, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h376 | h376
                          · linarith only [h371, h372, h376, hlam]
                          · linarith only [h339, h369, h370, h372, h376, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h379 | h379
                      · linarith only [h371, h379, h4, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h381 | h381
                        · linarith only [h1, h2, h367, h370, h379, h381, hc23, hlam, hphi, u3elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h383 | h383
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h384 | h384
                            · linarith only [h339, h369, h370, h379, h384, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · linarith only [h370, h371, h384, hc23, hlam, hphi, u3elo3]
                          · linarith only [h339, h369, h370, h371, h383, hc23, hlam, hphi, u3elo3]
                  · linarith only [h3, h339, h369, h370, h4, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h389 | h389
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h390 | h390
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h391 | h391
                      · linarith only [h0, h391, h4, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h393 | h393
                        · linarith only [h1, h3, h367, h393, h4, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h395 | h395
                          · linarith only [h0, h1, h339, h367, h369, h390, h395, h4, hc13, hlam, hphi, u3elo4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h397 | h397
                            · linarith only [h1, h339, h389, h397, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h399 | h399
                              · linarith only [h1, h339, h367, h389, h399, h4, hc02, hlam, hphi, ht23, u3elo3]
                              · linarith only [h0, h390, h397, h399, h4, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h402 | h402
                      · linarith only [h0, h4, h402, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h404 | h404
                        · linarith only [h1, h339, h367, h404, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h406 | h406
                          · linarith only [h2, h369, h406, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h408 | h408
                            · linarith only [h1, h339, h408, hc13, hlam, hphi, u3elo2]
                            · linarith only [h389, h390, h408, hc23, hlam, hphi, u3elo3]
                  · linarith only [h3, h367, h389, h4, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h412 | h412
          · linarith only [h3, h412, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h414 | h414
            · rcases m.htr 0 3 5 (by decide) (by decide) with h415 | h415
              · rcases m.htr 0 4 5 (by decide) (by decide) with h416 | h416
                · rcases m.htr 1 2 3 (by decide) (by decide) with h417 | h417
                  · linarith only [h0, h3, h417, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h419 | h419
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h420 | h420
                      · linarith only [h0, h412, h420, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h422 | h422
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h423 | h423
                          · linarith only [h0, h3, h419, h423, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h425 | h425
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h426 | h426
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h427 | h427
                                · linarith only [h419, h420, h423, h427, hlam]
                                · linarith only [h412, h414, h416, h427, hc02, hlam, hphi, ht23, u3elo0]
                              · linarith only [h3, h414, h416, h419, h420, h422, h423, h425, h426, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h3, h414, h416, h419, h420, h423, h425, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h415, h422, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h433 | h433
                      · linarith only [h0, h2, h3, h412, h433, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h435 | h435
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h436 | h436
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h437 | h437
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h438 | h438
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h439 | h439
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h440 | h440
                                  · linarith only [h3, h414, h440, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                                  · rcases h5bigk with h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [hlam, p442_0]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h412, h433, h437, h439, hc12, hlam, hphi, ht23, p442_1, u3elo2]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h412, hlam, p442_0]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h412, h437, h439, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p442_1, u3elo2, u5ehi3]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h412, h437, h439, h440, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p442_1, u3elo2]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h2, hlam, p442_0]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [hlam, p442_0]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h433, hlam, p442_0]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p442_1, u5ehi3]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h2, h412, h437, h439, h440, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p442_1, u3elo2]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h437, h439, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p442_1, u3elo2, u5ehi0]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h437, h439, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p442_1, u3elo2, u5ehi1]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [hlam, p442_0]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h437, h439, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p442_1, u3elo2, u5ehi3]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h437, h439, h440, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p442_1, u3elo2]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h415, hlam, p442_1]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h435, hlam, p442_1]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h438, hlam, p442_0]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [hlam, p442_0]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h440, hlam, p442_1]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h416, hlam, p442_0]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h436, hlam, p442_0]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h439, hlam, p442_0]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [h436, hc14, hlam, hphi, ht01, ht0b, ht5b, p442_1, u5ehi3]
                                    · have p442_0 := h442c.1
                                      have p442_1 := h442c.2.1
                                      have p442_2 := h442c.2.2.1
                                      have p442_3 := h442c.2.2.2
                                      linarith only [hlam, p442_0]
                                · linarith only [h3, h414, h416, h419, h439, hc12, hlam, hphi, ht23, u3elo2]
                              · linarith only [h3, h414, h416, h438, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                            · linarith only [h3, h414, h416, h437, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi4]
                          · linarith only [h414, h416, h419, h436, hc12, hlam, hphi, ht23, u3elo0]
                        · linarith only [h3, h415, h435, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h473 | h473
                  · linarith only [h0, h3, h473, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h475 | h475
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h476 | h476
                      · linarith only [h0, h3, h476, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h478 | h478
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h479 | h479
                          · linarith only [h0, h3, h416, h475, h479, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h481 | h481
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h482 | h482
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h483 | h483
                                · linarith only [h0, h412, h416, h475, h483, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h485 | h485
                                  · linarith only [h412, h483, h485, hc02, hlam, hphi, ht23, u3elo3]
                                  · rcases h5bigk with h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [hlam, p487_0]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h3, h415, h478, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p487_1, u3elo2, u5ehi3]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h412, hlam, p487_0]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h3, h415, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p487_1, u3elo2, u5ehi3]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h416, hlam, p487_1]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h2, hlam, p487_0]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [hlam, p487_0]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h476, hlam, p487_0]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p487_1, u5ehi3]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h479, hlam, p487_1]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h0, h412, h475, h481, h483, hc34, hc45, hlam, hphi, p487_1]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h475, h476, h481, h483, hc34, hc45, hlam, hphi, p487_1]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [hlam, p487_0]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h482, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p487_1, u3elo2, u5ehi3]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h483, hlam, p487_1]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h415, hlam, p487_1]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h478, hlam, p487_1]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h482, hlam, p487_0]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [hlam, p487_0]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h485, hlam, p487_1]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h0, h412, h475, h481, hc34, hc45, hlam, hphi, p487_1]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h475, h476, h481, hc34, hc45, hlam, hphi, p487_1]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [h0, h412, h475, h481, hc34, hc45, hlam, hphi, p487_1]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      rcases p487_3 (m.d 0 5) (by simp) with h511 | h511
                                      · linarith only [h416, h511, hlam]
                                      · linarith only [h415, h511, hlam]
                                    · have p487_0 := h487c.1
                                      have p487_1 := h487c.2.1
                                      have p487_2 := h487c.2.2.1
                                      have p487_3 := h487c.2.2.2
                                      linarith only [hlam, p487_0]
                              · linarith only [h3, h478, h482, hc03, hlam, hphi, u3elo1]
                            · linarith only [h3, h481, hc02, hlam, hphi, ht23, u3elo3]
                        · linarith only [h415, h478, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h518 | h518
                      · linarith only [h0, h412, h518, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h520 | h520
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h521 | h521
                          · linarith only [h2, h416, h521, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h523 | h523
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h524 | h524
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h525 | h525
                                · linarith only [h475, h521, h523, h525, hc12, hlam, hphi, ht23, u3elo2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h527 | h527
                                  · linarith only [h475, h525, h527, hc12, hlam, hphi, ht23, u3elo3]
                                  · rcases h5bigk with h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [hlam, p529_0]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [h3, h415, h520, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p529_1, u3elo2, u5ehi3]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [h412, hlam, p529_0]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [h3, h415, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p529_1, u3elo2, u5ehi3]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [h416, hlam, p529_1]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [h2, hlam, p529_0]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [hlam, p529_0]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [h518, hlam, p529_0]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p529_1, u5ehi3]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [h521, hlam, p529_1]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [h524, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p529_1, u3elo2, u5ehi0]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [h524, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p529_1, u3elo2, u5ehi1]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [hlam, p529_0]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [h524, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p529_1, u3elo2, u5ehi3]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [h525, hlam, p529_1]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [h415, hlam, p529_1]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [h520, hlam, p529_1]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [h524, hlam, p529_0]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [hlam, p529_0]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [h527, hlam, p529_1]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      rcases p529_3 (m.d 0 5) (by simp) with h550 | h550
                                      · linarith only [h416, h550, hlam]
                                      · rcases p529_3 (m.d 1 5) (by simp) with h552 | h552
                                        · linarith only [h521, h552, hlam]
                                        · rcases p529_3 (m.d 2 5) (by simp) with h554 | h554
                                          · linarith only [h525, h554, hlam]
                                          · linarith only [h412, h554, hlam]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      rcases p529_3 (m.d 0 5) (by simp) with h557 | h557
                                      · linarith only [h416, h557, hlam]
                                      · linarith only [h2, h557, hlam]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [h412, hc02, hc45, hlam, hphi, ht23, ht34, p529_1]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      rcases p529_3 (m.d 0 5) (by simp) with h561 | h561
                                      · linarith only [h416, h561, hlam]
                                      · linarith only [h415, h561, hlam]
                                    · have p529_0 := h529c.1
                                      have p529_1 := h529c.2.1
                                      have p529_2 := h529c.2.2.1
                                      have p529_3 := h529c.2.2.2
                                      linarith only [hlam, p529_0]
                              · linarith only [h3, h520, h524, hc03, hlam, hphi, u3elo1]
                            · linarith only [h1, h3, h520, h523, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                        · linarith only [h415, h520, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h568 | h568
                · linarith only [h414, h415, h568, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h570 | h570
                  · linarith only [h0, h3, h570, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h572 | h572
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h573 | h573
                      · linarith only [h0, h3, h415, h573, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h575 | h575
                        · linarith only [h3, h415, h575, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h577 | h577
                          · linarith only [h0, h3, h415, h568, h572, h577, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h579 | h579
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h580 | h580
                              · linarith only [h3, h415, h580, hc02, hlam, hphi, ht23, u3elo2]
                              · linarith only [h0, h3, h572, h579, h580, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                            · linarith only [h3, h579, hc02, hlam, hphi, ht23, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h584 | h584
                      · linarith only [h0, h412, h584, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h586 | h586
                        · linarith only [h1, h415, h586, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h588 | h588
                          · linarith only [h2, h568, h588, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h590 | h590
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h591 | h591
                              · linarith only [h1, h415, h591, hc13, hlam, hphi, u3elo2]
                              · linarith only [h3, h591, hc02, hlam, hphi, ht23, u3elo4]
                            · linarith only [h0, h3, h590, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h595 | h595
              · linarith only [h414, h595, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h597 | h597
                · rcases m.htr 1 2 3 (by decide) (by decide) with h598 | h598
                  · linarith only [h0, h3, h598, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h600 | h600
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h601 | h601
                      · linarith only [h0, h3, h412, h414, h601, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h603 | h603
                        · linarith only [h1, h414, h603, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h605 | h605
                          · linarith only [h0, h3, h414, h600, h605, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h607 | h607
                            · linarith only [h3, h414, h607, hc02, hlam, hphi, ht23, u3elo2]
                            · linarith only [h0, h3, h600, h607, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h610 | h610
                      · linarith only [h0, h412, h610, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h612 | h612
                        · linarith only [h3, h595, h612, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h614 | h614
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h615 | h615
                            · linarith only [h0, h3, h414, h615, hc12, hlam, hphi, ht23, u3elo2]
                            · linarith only [h0, h3, h615, hc12, hlam, hphi, ht23, u3elo3]
                          · linarith only [h414, h597, h600, h614, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h619 | h619
                  · linarith only [h0, h3, h619, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h621 | h621
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h622 | h622
                      · linarith only [h0, h2, h3, h412, h622, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h624 | h624
                        · linarith only [h1, h595, h624, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h626 | h626
                          · linarith only [h0, h3, h414, h597, h621, h626, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h628 | h628
                            · linarith only [h0, h3, h414, h621, h628, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · linarith only [h0, h3, h621, h628, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h631 | h631
                      · linarith only [h0, h412, h631, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h633 | h633
                        · linarith only [h1, h595, h633, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h635 | h635
                          · linarith only [h2, h597, h635, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h637 | h637
                            · linarith only [h3, h414, h637, hc02, hlam, hphi, ht23, u3elo2]
                            · linarith only [h0, h3, h637, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h640 | h640
        · rcases m.htr 0 2 5 (by decide) (by decide) with h641 | h641
          · linarith only [h0, h2, h641, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h643 | h643
            · rcases m.htr 0 3 5 (by decide) (by decide) with h644 | h644
              · linarith only [h1, h2, h644, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h646 | h646
                · linarith only [h643, h644, h646, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h648 | h648
                  · linarith only [h0, h2, h644, h648, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h2, h640, h644, h648, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h651 | h651
              · linarith only [h643, h651, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h653 | h653
                · rcases m.htr 1 2 3 (by decide) (by decide) with h654 | h654
                  · linarith only [h0, h2, h643, h653, h654, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h2, h640, h643, h653, h654, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h657 | h657
                  · linarith only [h0, h2, h651, h657, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h2, h640, h651, h657, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h660 | h660
          · linarith only [h640, h660, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h662 | h662
            · rcases m.htr 0 3 5 (by decide) (by decide) with h663 | h663
              · linarith only [h1, h2, h663, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h665 | h665
                · linarith only [h662, h663, h665, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h667 | h667
                  · linarith only [h0, h640, h663, h667, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h669 | h669
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h670 | h670
                      · linarith only [h0, h640, h660, h670, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h672 | h672
                        · linarith only [h1, h2, h640, h663, h672, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h1, h2, h667, h669, h672, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h675 | h675
                      · linarith only [h1, h2, h667, h675, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h677 | h677
                        · linarith only [h1, h2, h663, h677, hlam]
                        · linarith only [h1, h2, h667, h677, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h680 | h680
              · linarith only [h662, h680, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h682 | h682
                · rcases m.htr 1 2 3 (by decide) (by decide) with h683 | h683
                  · linarith only [h0, h2, h640, h683, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h685 | h685
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h686 | h686
                      · linarith only [h1, h2, h662, h682, h683, h686, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h688 | h688
                        · linarith only [h1, h2, h662, h682, h688, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                        · linarith only [h1, h2, h683, h688, hc12, hlam, hphi, ht23, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h691 | h691
                      · linarith only [h1, h2, h683, h691, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h693 | h693
                        · linarith only [h1, h2, h693, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h1, h2, h683, h693, hc12, hlam, hphi, ht23, u3elo4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h696 | h696
                  · linarith only [h0, h2, h680, h696, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h698 | h698
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h699 | h699
                      · linarith only [h0, h2, h680, h699, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h701 | h701
                        · linarith only [h1, h2, h680, h701, hlam]
                        · linarith only [h1, h2, h696, h701, hc12, hlam, hphi, ht23, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h704 | h704
                      · linarith only [h1, h2, h660, h696, h704, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h706 | h706
                        · linarith only [h1, h2, h706, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h1, h2, h696, h706, hc12, hlam, hphi, ht23, u3elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h710 | h710
    · rcases m.htr 0 1 5 (by decide) (by decide) with h711 | h711
      · rcases m.htr 0 2 3 (by decide) (by decide) with h712 | h712
        · rcases m.htr 0 2 5 (by decide) (by decide) with h713 | h713
          · rcases m.htr 0 3 4 (by decide) (by decide) with h714 | h714
            · rcases m.htr 0 3 5 (by decide) (by decide) with h715 | h715
              · rcases m.htr 0 4 5 (by decide) (by decide) with h716 | h716
                · rcases m.htr 1 2 3 (by decide) (by decide) with h717 | h717
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h718 | h718
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h719 | h719
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h720 | h720
                        · linarith only [h0, h710, h720, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h715, h720, hc13, hlam, hphi, u3elo0]
                      · linarith only [h0, h711, h719, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h710, h714, h716, h718, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h710, h714, h716, h717, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h726 | h726
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h727 | h727
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h728 | h728
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h729 | h729
                        · linarith only [h0, h710, h729, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h715, h726, h729, hc23, hlam, hphi, u3elo0]
                      · linarith only [h0, h711, h728, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h710, h715, h727, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h710, h715, h726, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h735 | h735
                · linarith only [h714, h715, h735, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h737 | h737
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h738 | h738
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h739 | h739
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h740 | h740
                        · linarith only [h710, h715, h740, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h742 | h742
                          · linarith only [h711, h735, h742, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h744 | h744
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h745 | h745
                              · linarith only [h710, h715, h737, h745, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h747 | h747
                                · linarith only [h738, h742, h747, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h749 | h749
                                  · linarith only [h710, h715, h735, h737, h744, h749, hlam]
                                  · rcases h5bigk with h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [hlam, p751_0]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [h0, h711, hc12, hlam, hphi, ht01, ht0b, ht5b, p751_1, u5ehi1]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [h0, h711, hc12, hlam, hphi, ht01, ht0b, ht5b, p751_1, u5ehi2]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [h715, hlam, p751_0]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [h735, hlam, p751_1]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [h711, hlam, p751_0]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [hlam, p751_0]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [h0, h711, hc12, hlam, hphi, ht01, ht0b, ht5b, p751_1, u5ehi2]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [h740, hlam, p751_0]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [h742, hlam, p751_1]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [h713, hlam, p751_1]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [h739, hlam, p751_1]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [hlam, p751_0]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [h745, hlam, p751_1]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [h747, hlam, p751_1]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p751_1, u3elo4, u5ehi0]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p751_1, u3elo4, u5ehi1]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p751_1, u3elo4, u5ehi2]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [hlam, p751_0]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [h749, hlam, p751_1]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [h710, h715, h737, h744, hc34, hc45, hlam, hphi, p751_1]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [h737, h740, h744, hc34, hc45, hlam, hphi, p751_1]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [h744, h745, hc34, hc45, hlam, hphi, p751_1]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [h710, h715, h737, h744, hc34, hc45, hlam, hphi, p751_1]
                                    · have p751_0 := h751c.1
                                      have p751_1 := h751c.2.1
                                      have p751_2 := h751c.2.2.1
                                      have p751_3 := h751c.2.2.2
                                      linarith only [hlam, p751_0]
                            · linarith only [h714, h715, h744, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h711, h739, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h711, h738, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h711, h737, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h781 | h781
              · linarith only [h714, h781, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h783 | h783
                · rcases m.htr 1 2 3 (by decide) (by decide) with h784 | h784
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h785 | h785
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h786 | h786
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h787 | h787
                        · linarith only [h0, h710, h781, h787, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h789 | h789
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h790 | h790
                            · linarith only [h710, h714, h784, h790, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h792 | h792
                              · linarith only [h710, h781, h784, h792, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h794 | h794
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h795 | h795
                                  · rcases h5bigk with h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [hlam, p796_0]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h0, h711, hc12, hlam, hphi, ht01, ht0b, ht5b, p796_1, u5ehi1]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h0, h711, hc12, hlam, hphi, ht01, ht0b, ht5b, p796_1, u5ehi2]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h781, hlam, p796_0]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h781, h795, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p796_1, u3elo3, u5ehi4]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h711, hlam, p796_0]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [hlam, p796_0]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h0, h711, hc12, hlam, hphi, ht01, ht0b, ht5b, p796_1, u5ehi2]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h787, hlam, p796_0]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h0, h711, hc12, hlam, hphi, ht01, ht0b, ht5b, p796_1, u5ehi4]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h713, hlam, p796_1]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h786, hlam, p796_1]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [hlam, p796_0]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h792, hlam, p796_1]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h0, h713, hc12, hlam, hphi, ht01, ht0b, ht5b, p796_1, u5ehi4]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h795, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p796_1, u3elo3, u5ehi0]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h795, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p796_1, u3elo3, u5ehi1]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h795, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p796_1, u3elo3, u5ehi2]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [hlam, p796_0]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h795, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p796_1, u3elo3, u5ehi4]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h783, hlam, p796_0]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h789, hlam, p796_0]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h794, hlam, p796_0]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [h795, hlam, p796_0]
                                    · have p796_0 := h796c.1
                                      have p796_1 := h796c.2.1
                                      have p796_2 := h796c.2.2.1
                                      have p796_3 := h796c.2.2.2
                                      linarith only [hlam, p796_0]
                                  · linarith only [h714, h783, h795, hlam]
                                · linarith only [h714, h783, h790, h794, hc23, hlam, hphi, u3elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h824 | h824
                            · linarith only [h710, h714, h783, h784, h785, h789, h824, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                            · linarith only [h714, h783, h785, h789, h824, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h711, h786, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h711, h785, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h711, h784, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h830 | h830
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h831 | h831
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h832 | h832
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h833 | h833
                        · linarith only [h710, h781, h833, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h835 | h835
                          · linarith only [h711, h783, h835, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h837 | h837
                            · linarith only [h710, h714, h830, h837, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h839 | h839
                              · linarith only [h0, h711, h831, h835, h837, h839, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h841 | h841
                                · linarith only [h0, h711, h831, h835, h841, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h843 | h843
                                  · linarith only [h714, h783, h843, hc03, hlam, hphi, u3elo3]
                                  · rcases h5bigk with h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [hlam, p845_0]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [h781, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p845_1, u3elo4, u5ehi1]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [h781, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p845_1, u3elo4, u5ehi2]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [h781, hlam, p845_0]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [h783, hlam, p845_1]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [h711, hlam, p845_0]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [hlam, p845_0]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [h0, h711, hc12, hlam, hphi, ht01, ht0b, ht5b, p845_1, u5ehi2]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [h833, hlam, p845_0]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [h835, hlam, p845_1]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [h713, hlam, p845_1]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [h832, hlam, p845_1]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [hlam, p845_0]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [h839, hlam, p845_1]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [h841, hlam, p845_1]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p845_1, u3elo4, u5ehi0]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p845_1, u3elo4, u5ehi1]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p845_1, u3elo4, u5ehi2]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [hlam, p845_0]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [h843, hlam, p845_1]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      rcases p845_3 (m.d 0 5) (by simp) with h866 | h866
                                      · linarith only [h783, h866, hlam]
                                      · rcases p845_3 (m.d 1 5) (by simp) with h868 | h868
                                        · linarith only [h835, h868, hlam]
                                        · rcases p845_3 (m.d 2 5) (by simp) with h870 | h870
                                          · linarith only [h841, h870, hlam]
                                          · rcases p845_3 (m.d 3 5) (by simp) with h872 | h872
                                            · linarith only [h843, h872, hlam]
                                            · linarith only [h781, h872, hlam]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      rcases p845_3 (m.d 0 5) (by simp) with h875 | h875
                                      · linarith only [h783, h875, hlam]
                                      · linarith only [h711, h875, hlam]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      rcases p845_3 (m.d 0 5) (by simp) with h878 | h878
                                      · linarith only [h783, h878, hlam]
                                      · linarith only [h713, h878, hlam]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [h710, h781, h830, hc23, hc45, hlam, hphi, ht34, p845_1]
                                    · have p845_0 := h845c.1
                                      have p845_1 := h845c.2.1
                                      have p845_2 := h845c.2.2.1
                                      have p845_3 := h845c.2.2.2
                                      linarith only [hlam, p845_0]
                      · linarith only [h0, h711, h832, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h711, h831, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h711, h830, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
          · linarith only [h0, h711, h713, hlam]
        · linarith only [h0, h711, h712, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h888 | h888
        · rcases m.htr 0 2 5 (by decide) (by decide) with h889 | h889
          · rcases m.htr 0 3 4 (by decide) (by decide) with h890 | h890
            · rcases m.htr 0 3 5 (by decide) (by decide) with h891 | h891
              · linarith only [h710, h711, h891, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h893 | h893
                · linarith only [h890, h891, h893, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h895 | h895
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h896 | h896
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h897 | h897
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h898 | h898
                        · linarith only [h710, h711, h891, h897, h898, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h710, h711, h898, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h710, h889, h895, h897, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h902 | h902
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h903 | h903
                        · linarith only [h710, h711, h891, h902, h903, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                        · linarith only [h710, h711, h895, h903, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h889, h902, hlam]
                  · linarith only [h0, h889, h895, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h908 | h908
              · linarith only [h890, h908, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h910 | h910
                · rcases m.htr 1 2 3 (by decide) (by decide) with h911 | h911
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h912 | h912
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h913 | h913
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h914 | h914
                        · linarith only [h710, h711, h908, h913, h914, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h710, h711, h911, h914, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h710, h889, h911, h913, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h918 | h918
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h919 | h919
                        · linarith only [h710, h711, h918, h919, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h710, h711, h919, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h889, h918, hlam]
                  · linarith only [h0, h911, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h924 | h924
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h925 | h925
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h926 | h926
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h927 | h927
                        · linarith only [h710, h711, h926, h927, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h710, h711, h927, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h889, h926, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h931 | h931
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h932 | h932
                        · linarith only [h710, h711, h908, h910, h925, h931, h932, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h710, h711, h924, h932, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h889, h931, hlam]
                  · linarith only [h0, h889, h924, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h937 | h937
            · rcases m.htr 0 3 5 (by decide) (by decide) with h938 | h938
              · linarith only [h0, h710, h889, h938, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h940 | h940
                · linarith only [h937, h938, h940, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h942 | h942
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h943 | h943
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h944 | h944
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h945 | h945
                        · linarith only [h0, h710, h889, h937, h938, h944, h945, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h710, h711, h945, hc13, hlam, hphi, u3elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h948 | h948
                        · linarith only [h0, h710, h889, h938, h944, h948, hc02, hc25, hlam, hphi]
                        · linarith only [h0, h710, h942, h944, h948, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h951 | h951
                      · linarith only [h0, h710, h889, h942, h943, h951, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h953 | h953
                        · linarith only [h0, h710, h943, h953, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h0, h710, h942, h951, h953, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h710, h942, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h957 | h957
              · linarith only [h937, h957, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h959 | h959
                · rcases m.htr 1 2 3 (by decide) (by decide) with h960 | h960
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h961 | h961
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h962 | h962
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h963 | h963
                        · linarith only [h0, h710, h889, h957, h962, h963, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h710, h711, h960, h963, hc23, hlam, hphi, u3elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h966 | h966
                        · linarith only [h0, h710, h962, h966, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h0, h710, h962, h966, hc13, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h969 | h969
                      · linarith only [h889, h961, h969, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h971 | h971
                        · linarith only [h0, h710, h961, h971, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h710, h711, h960, h971, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h710, h960, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h975 | h975
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h976 | h976
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h977 | h977
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h978 | h978
                        · linarith only [h0, h710, h978, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h0, h710, h889, h977, h978, hc13, hlam, hphi, u3elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h981 | h981
                        · linarith only [h0, h710, h977, h981, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h710, h711, h975, h981, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h984 | h984
                      · linarith only [h0, h710, h889, h975, h976, h984, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h986 | h986
                        · linarith only [h0, h710, h957, h976, h986, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                        · linarith only [h0, h710, h975, h984, h986, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h710, h975, hc13, hlam, hphi, u3elo2]
        · linarith only [h0, h710, h888, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h991 | h991
      · linarith only [h710, h991, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h993 | h993
        · rcases m.htr 0 2 5 (by decide) (by decide) with h994 | h994
          · rcases m.htr 0 3 4 (by decide) (by decide) with h995 | h995
            · rcases m.htr 0 3 5 (by decide) (by decide) with h996 | h996
              · rcases m.htr 0 4 5 (by decide) (by decide) with h997 | h997
                · rcases m.htr 1 2 3 (by decide) (by decide) with h998 | h998
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h999 | h999
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1000 | h1000
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1001 | h1001
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1002 | h1002
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1003 | h1003
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1004 | h1004
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1005 | h1005
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1006 | h1006
                                  · linarith only [h1003, h1006, h993, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases h5bigk with h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [hlam, p1008_0]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h991, hlam, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h1001, h1005, h1006, h991, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1008_1, u3elo1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h710, h995, h997, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1008_1, u3elo1, u5ehi3]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h1006, h710, h995, h997, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1008_1, u3elo1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h1001, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1008_1, u3elo1, u5ehi0]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [hlam, p1008_0]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h1001, h1005, h1006, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1008_1, u3elo1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h1001, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1008_1, u3elo1, u5ehi3]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h1001, h1006, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1008_1, u3elo1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h994, hlam, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h1000, hlam, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [hlam, p1008_0]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h1001, h991, h994, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1008_1, u3elo1, u5ehi3]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h1006, h710, h994, h995, h997, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1008_1, u3elo1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h996, hlam, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h1001, hlam, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h1004, hlam, p1008_0]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [hlam, p1008_0]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h1006, hlam, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h997, hlam, p1008_0]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h1002, hlam, p1008_0]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h1005, hlam, p1008_0]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h710, h995, h997, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1008_1, u3elo1, u5ehi3]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [hlam, p1008_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1034 | h1034
                                  · linarith only [h1005, h1034, h710, h995, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                  · rcases h5bigk with h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [hlam, p1036_0]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h991, hlam, p1036_1]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h710, h995, h997, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1036_1, u3elo1, u5ehi2]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h710, h995, h997, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1036_1, u3elo1, u5ehi3]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h1003, h1005, h710, h995, h997, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1036_1, u3elo1]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h1001, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1036_1, u3elo1, u5ehi0]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [hlam, p1036_0]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h1001, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1036_1, u3elo1, u5ehi2]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h1001, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1036_1, u3elo1, u5ehi3]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h1001, h1003, h1005, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1036_1, u3elo1]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h994, hlam, p1036_1]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h1000, hlam, p1036_1]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [hlam, p1036_0]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h0, h994, hc12, hlam, hphi, ht01, ht0b, ht5b, p1036_1, u5ehi3]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h1005, hlam, p1036_1]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h996, hlam, p1036_1]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h1001, hlam, p1036_1]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h1004, hlam, p1036_0]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [hlam, p1036_0]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h1034, hlam, p1036_1]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h997, hlam, p1036_0]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h1002, hlam, p1036_0]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h1001, h991, h997, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1036_1, u3elo1, u5ehi2]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [h710, h995, h997, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1036_1, u3elo1, u5ehi3]
                                    · have p1036_0 := h1036c.1
                                      have p1036_1 := h1036c.2.1
                                      have p1036_2 := h1036c.2.2.1
                                      have p1036_3 := h1036c.2.2.2
                                      linarith only [hlam, p1036_0]
                              · linarith only [h1004, h710, h996, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1003, h710, h995, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1002, h710, h991, h995, h997, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1001, h710, h996, hlam]
                      · linarith only [h0, h1000, h994, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1067 | h1067
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1068 | h1068
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1069 | h1069
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1070 | h1070
                            · linarith only [h0, h1070, h994, h999, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                            · linarith only [h1070, h710, h995, hc23, hlam, hphi, u3elo1]
                          · linarith only [h0, h1069, h993, h995, h997, h999, hlam]
                        · linarith only [h1068, h710, h996, hlam]
                      · linarith only [h0, h1067, h994, hlam]
                  · linarith only [h0, h994, h998, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1077 | h1077
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1078 | h1078
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1079 | h1079
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1080 | h1080
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1081 | h1081
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1082 | h1082
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1083 | h1083
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1084 | h1084
                                · linarith only [h1084, h994, h997, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1086 | h1086
                                  · linarith only [h1086, h995, h997, hlam]
                                  · rcases h5bigk with h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [hlam, p1088_0]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h991, hlam, p1088_1]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h1083, h710, h996, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1088_1, u3elo1, u5ehi3]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h710, h996, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1088_1, u3elo1, u5ehi3]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h997, hlam, p1088_1]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h1080, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1088_1, u3elo1, u5ehi0]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [hlam, p1088_0]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h1080, h1083, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1088_1, u3elo1, u5ehi3]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h1080, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1088_1, u3elo1, u5ehi3]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h1080, h1083, h994, h997, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1088_1, u3elo1, u5ehi3]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h994, hlam, p1088_1]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h1079, hlam, p1088_1]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [hlam, p1088_0]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h1080, h991, h994, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1088_1, u3elo1, u5ehi3]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h1084, hlam, p1088_1]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h996, hlam, p1088_1]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h1080, hlam, p1088_1]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h1083, hlam, p1088_0]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [hlam, p1088_0]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h1086, hlam, p1088_1]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h1078, h1081, hc12, hlam, hphi, ht01, ht0b, ht5b, p1088_1, u5ehi0]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h1081, hlam, p1088_0]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h1080, h1081, h1083, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1088_1, u3elo1, u5ehi3]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [h1080, h1081, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1088_1, u3elo1, u5ehi3]
                                    · have p1088_0 := h1088c.1
                                      have p1088_1 := h1088c.2.1
                                      have p1088_2 := h1088c.2.2.1
                                      have p1088_3 := h1088c.2.2.2
                                      linarith only [hlam, p1088_0]
                              · linarith only [h1083, h710, h996, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1082, h710, h995, hc23, hlam, hphi, u3elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1116 | h1116
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1117 | h1117
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1118 | h1118
                                · linarith only [h1078, h1081, h1118, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1120 | h1120
                                  · linarith only [h1081, h1120, h710, h995, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                  · rcases h5bigk with h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [hlam, p1122_0]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [h991, hlam, p1122_1]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [h710, h996, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1122_1, u3elo1, u5ehi2]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [h710, h996, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1122_1, u3elo1, u5ehi3]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [h997, hlam, p1122_1]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [h1080, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1122_1, u3elo1, u5ehi0]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [hlam, p1122_0]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [h1080, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1122_1, u3elo1, u5ehi2]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [h1080, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1122_1, u3elo1, u5ehi3]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [h1081, hlam, p1122_1]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [h994, hlam, p1122_1]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [h1079, hlam, p1122_1]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [hlam, p1122_0]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [h1080, h991, h994, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1122_1, u3elo1, u5ehi3]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [h1118, hlam, p1122_1]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [h996, hlam, p1122_1]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [h1080, hlam, p1122_1]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [h1117, hlam, p1122_0]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [hlam, p1122_0]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [h1120, hlam, p1122_1]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      rcases p1122_3 (m.d 0 5) (by simp) with h1143 | h1143
                                      · linarith only [h1143, h997, hlam]
                                      · rcases p1122_3 (m.d 1 5) (by simp) with h1145 | h1145
                                        · linarith only [h1081, h1145, hlam]
                                        · linarith only [h1145, h991, hlam]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [h991, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1122_1]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      rcases p1122_3 (m.d 0 5) (by simp) with h1149 | h1149
                                      · linarith only [h1149, h997, hlam]
                                      · linarith only [h1149, h994, hlam]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      rcases p1122_3 (m.d 0 5) (by simp) with h1152 | h1152
                                      · linarith only [h1152, h997, hlam]
                                      · linarith only [h1152, h996, hlam]
                                    · have p1122_0 := h1122c.1
                                      have p1122_1 := h1122c.2.1
                                      have p1122_2 := h1122c.2.2.1
                                      have p1122_3 := h1122c.2.2.2
                                      linarith only [hlam, p1122_0]
                              · linarith only [h1117, h710, h996, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1116, h710, h995, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1080, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1079, h994, h996, hc01, hlam, hphi, ht12, ht23, u3elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1160 | h1160
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1161 | h1161
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1162 | h1162
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1163 | h1163
                            · linarith only [h0, h1078, h1163, h994, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                            · linarith only [h1163, h710, h995, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1077, h1078, h1161, h1162, hlam]
                        · linarith only [h1161, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1160, h994, hlam]
                  · linarith only [h0, h1077, h994, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1170 | h1170
                · linarith only [h1170, h995, h996, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1172 | h1172
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1173 | h1173
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1174 | h1174
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1175 | h1175
                        · linarith only [h1175, h996, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1175, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1174, h994, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1179 | h1179
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1180 | h1180
                        · linarith only [h1180, h995, h996, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h1180, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1179, h994, hlam]
                  · linarith only [h0, h1172, h993, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1185 | h1185
              · linarith only [h1185, h995, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1187 | h1187
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1188 | h1188
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1189 | h1189
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1190 | h1190
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1191 | h1191
                        · linarith only [h1185, h1191, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1191, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1190, h994, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1195 | h1195
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1196 | h1196
                        · linarith only [h1185, h1196, h710, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1196, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1195, h994, hlam]
                  · linarith only [h0, h1188, h993, h994, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1201 | h1201
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1202 | h1202
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1203 | h1203
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1204 | h1204
                        · linarith only [h1185, h1204, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1204, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1203, h994, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1208 | h1208
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1209 | h1209
                        · linarith only [h1185, h1209, h710, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1209, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1208, h994, hlam]
                  · linarith only [h0, h1187, h1201, h993, h994, h995, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1214 | h1214
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1215 | h1215
              · linarith only [h1215, h993, h994, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1217 | h1217
                · linarith only [h1214, h1215, h1217, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1219 | h1219
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1220 | h1220
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1221 | h1221
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1222 | h1222
                        · linarith only [h1215, h1222, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1222, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1225 | h1225
                        · linarith only [h1214, h1215, h1225, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h1225, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1228 | h1228
                      · linarith only [h1220, h1228, h993, h994, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1230 | h1230
                        · linarith only [h1214, h1215, h1230, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h1230, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h0, h1219, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1234 | h1234
              · linarith only [h1214, h1234, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1236 | h1236
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1237 | h1237
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1238 | h1238
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1239 | h1239
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1240 | h1240
                        · linarith only [h1234, h1240, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1240, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1243 | h1243
                        · linarith only [h1234, h1243, h710, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1243, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1246 | h1246
                      · linarith only [h1238, h1246, h994, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1248 | h1248
                        · linarith only [h1234, h1248, h710, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1248, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h0, h1237, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1252 | h1252
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1253 | h1253
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1254 | h1254
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1255 | h1255
                        · linarith only [h1234, h1255, h993, h994, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1255, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1258 | h1258
                        · linarith only [h1234, h1258, h710, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1258, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1261 | h1261
                      · linarith only [h1253, h1261, h993, h994, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1263 | h1263
                        · linarith only [h1234, h1263, h710, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1263, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h0, h1252, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1267 | h1267
          · linarith only [h1267, h993, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1269 | h1269
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1270 | h1270
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1271 | h1271
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1272 | h1272
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1273 | h1273
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1274 | h1274
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1275 | h1275
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1276 | h1276
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1277 | h1277
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1278 | h1278
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1279 | h1279
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1280 | h1280
                                  · linarith only [h1269, h1280, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                                  · rcases h5bigk with h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [hlam, p1282_0]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h991, hlam, p1282_1]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1267, hlam, p1282_0]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1275, h991, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1282_1, u3elo1, u5ehi3]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1267, h1272, h1277, h1279, h1280, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1282_1, u3elo1]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1275, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1282_1, u3elo1, u5ehi0]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [hlam, p1282_0]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1275, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1282_1, u3elo1, u5ehi2]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1275, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1282_1, u3elo1, u5ehi3]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1275, h1280, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1282_1, u3elo1]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1271, h1274, h1280, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1282_1]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1274, hlam, p1282_1]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [hlam, p1282_0]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1274, h1275, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1282_1, u3elo1, u5ehi3]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1272, h1277, h1279, h1280, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1282_1, u3elo1]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1270, hlam, p1282_1]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1275, hlam, p1282_1]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1278, hlam, p1282_0]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [hlam, p1282_0]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1280, hlam, p1282_1]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1271, hlam, p1282_0]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1276, hlam, p1282_0]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1279, hlam, p1282_0]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [h1271, hc04, hlam, hphi, ht0b, ht5b, p1282_1, u5ehi3]
                                    · have p1282_0 := h1282c.1
                                      have p1282_1 := h1282c.2.1
                                      have p1282_2 := h1282c.2.2.1
                                      have p1282_3 := h1282c.2.2.2
                                      linarith only [hlam, p1282_0]
                                · linarith only [h0, h1267, h1269, h1271, h1272, h1279, h993, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · linarith only [h0, h1278, h993, hc01, hlam, hphi, ht12, ht23, u3elo4]
                            · linarith only [h1269, h1271, h1277, h993, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi4]
                          · linarith only [h1269, h1271, h1276, h991, hc01, hlam, hphi, ht12, ht23, u3elo0]
                        · linarith only [h1269, h1271, h1272, h1275, h993, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                      · linarith only [h1269, h1271, h1272, h1274, h993, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h1269, h1271, h1272, h1273, h993, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h1272, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1316 | h1316
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1317 | h1317
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1318 | h1318
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1319 | h1319
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1320 | h1320
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1321 | h1321
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1322 | h1322
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1323 | h1323
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1324 | h1324
                                  · linarith only [h1269, h1271, h1324, hlam]
                                  · rcases h5bigk with h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [hlam, p1326_0]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h991, hlam, p1326_1]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1267, hlam, p1326_0]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1319, h991, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1326_1, u3elo1, u5ehi3]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1271, hlam, p1326_1]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1319, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1326_1, u3elo1, u5ehi0]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [hlam, p1326_0]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1319, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1326_1, u3elo1, u5ehi2]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1319, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1326_1, u3elo1, u5ehi3]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1269, h1271, h1319, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1326_1, u3elo1]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1270, h1318, hc12, hlam, hphi, ht01, ht0b, ht5b, p1326_1, u5ehi3]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1318, hlam, p1326_1]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [hlam, p1326_0]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1318, h1319, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1326_1, u3elo1, u5ehi3]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1269, h1271, h1316, h1321, h1323, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1326_1, u3elo1]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1270, hlam, p1326_1]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1319, hlam, p1326_1]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1322, hlam, p1326_0]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [hlam, p1326_0]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1324, hlam, p1326_1]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1270, h1320, hc14, hlam, hphi, ht01, ht0b, ht5b, p1326_1, u5ehi3]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1320, hlam, p1326_0]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1323, hlam, p1326_0]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [h1316, h1321, h1323, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1326_1, u3elo1, u5ehi3]
                                    · have p1326_0 := h1326c.1
                                      have p1326_1 := h1326c.2.1
                                      have p1326_2 := h1326c.2.2.1
                                      have p1326_3 := h1326c.2.2.2
                                      linarith only [hlam, p1326_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1352 | h1352
                                  · linarith only [h0, h1267, h1323, h1352, hc01, hlam, hphi, ht12, ht23, u3elo3]
                                  · rcases h5bigk with h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [hlam, p1354_0]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h991, hlam, p1354_1]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h1267, hlam, p1354_0]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h1319, h991, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1354_1, u3elo1, u5ehi3]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h1271, hlam, p1354_1]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h1319, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1354_1, u3elo1, u5ehi0]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [hlam, p1354_0]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h0, h1267, h1319, hc01, hlam, hphi, ht12, ht23, p1354_1, u3elo1]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h1319, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1354_1, u3elo1, u5ehi3]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h0, h1267, h1319, h1323, hc01, hlam, hphi, ht12, ht23, p1354_1, u3elo1]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h1270, h1318, hc12, hlam, hphi, ht01, ht0b, ht5b, p1354_1, u5ehi3]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h1318, hlam, p1354_1]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [hlam, p1354_0]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h1319, h1320, h1323, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1354_1, u3elo1, u5ehi3]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h1323, hlam, p1354_1]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h1270, hlam, p1354_1]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h1319, hlam, p1354_1]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h1322, hlam, p1354_0]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [hlam, p1354_0]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h1352, hlam, p1354_1]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h1270, h1319, h1320, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1354_1, u3elo1, u5ehi3]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h1320, hlam, p1354_0]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h1319, h1320, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1354_1, u3elo1, u5ehi2]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [h1319, h1320, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1354_1, u3elo1, u5ehi3]
                                    · have p1354_0 := h1354c.1
                                      have p1354_1 := h1354c.2.1
                                      have p1354_2 := h1354c.2.2.1
                                      have p1354_3 := h1354c.2.2.2
                                      linarith only [hlam, p1354_0]
                              · linarith only [h0, h1322, h993, hc01, hlam, hphi, ht12, ht23, u3elo4]
                            · linarith only [h1270, h1321, h993, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1382 | h1382
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1383 | h1383
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1384 | h1384
                                · linarith only [h1317, h1320, h1384, h991, hc01, hc12, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1386 | h1386
                                  · linarith only [h1320, h1386, h991, hc01, hlam, hphi, ht12, ht23, u3elo3]
                                  · rcases h5bigk with h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [hlam, p1388_0]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h991, hlam, p1388_1]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h1267, hlam, p1388_0]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h1270, h1316, h993, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1388_1, u3elo1, u5ehi3]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h1271, hlam, p1388_1]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h1319, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1388_1, u3elo1, u5ehi0]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [hlam, p1388_0]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h0, h1267, h1319, hc01, hlam, hphi, ht12, ht23, p1388_1, u3elo1]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h1319, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1388_1, u3elo1, u5ehi3]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h1320, hlam, p1388_1]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h1270, h1318, hc12, hlam, hphi, ht01, ht0b, ht5b, p1388_1, u5ehi3]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h1318, hlam, p1388_1]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [hlam, p1388_0]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h1318, h1319, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1388_1, u3elo1, u5ehi3]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h1384, hlam, p1388_1]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h1270, hlam, p1388_1]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h1319, hlam, p1388_1]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h1383, hlam, p1388_0]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [hlam, p1388_0]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h1386, hlam, p1388_1]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      rcases p1388_3 (m.d 0 5) (by simp) with h1409 | h1409
                                      · linarith only [h1271, h1409, hlam]
                                      · rcases p1388_3 (m.d 1 5) (by simp) with h1411 | h1411
                                        · linarith only [h1320, h1411, hlam]
                                        · linarith only [h1411, h991, hlam]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h991, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1388_1]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [h0, h1267, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1388_1]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      rcases p1388_3 (m.d 0 5) (by simp) with h1416 | h1416
                                      · linarith only [h1271, h1416, hlam]
                                      · linarith only [h1270, h1416, hlam]
                                    · have p1388_0 := h1388c.1
                                      have p1388_1 := h1388c.2.1
                                      have p1388_2 := h1388c.2.2.1
                                      have p1388_3 := h1388c.2.2.2
                                      linarith only [hlam, p1388_0]
                              · linarith only [h0, h1383, h993, hc01, hlam, hphi, ht12, ht23, u3elo4]
                            · linarith only [h1269, h1382, h993, hlam]
                        · linarith only [h1270, h1319, hc13, hlam, hphi, u3elo0]
                      · linarith only [h1270, h1316, h1318, h993, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h1270, h1316, h1317, h993, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h1316, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1426 | h1426
                · linarith only [h1269, h1270, h1426, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1428 | h1428
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1429 | h1429
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1430 | h1430
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1431 | h1431
                        · linarith only [h1270, h1431, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1431, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1428, h1430, h993, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h1428, h1429, h993, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h1428, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1437 | h1437
              · linarith only [h1269, h1437, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1439 | h1439
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1440 | h1440
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1441 | h1441
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1442 | h1442
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1443 | h1443
                        · linarith only [h1437, h1443, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1443, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1440, h1442, h993, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h1440, h1441, h993, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h1440, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1449 | h1449
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1450 | h1450
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1451 | h1451
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1452 | h1452
                        · linarith only [h0, h1437, h1452, h993, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1452, h710, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1449, h1451, h993, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h1449, h1450, h993, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h1449, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem n7l_sBT3_H_L_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0elo := hb0.1
  have h5bigk := hb5.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h4, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h12, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h15 | h15
                  · linarith only [h15, h6, h7, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h17, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h17, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h20 | h20
                · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
                    · linarith only [h0, h22, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h22, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h20, h21, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                    · linarith only [h0, h27, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h27, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
                    · linarith only [h0, h30, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h30, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h33 | h33
              · rcases m.htr 0 3 5 (by decide) (by decide) with h34 | h34
                · linarith only [h34, h4, h5, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h36 | h36
                  · linarith only [h33, h34, h36, h4, h5, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
                    · linarith only [h0, h38, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h38, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h41 | h41
                · linarith only [h33, h4, h41, h5, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h43 | h43
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                    · linarith only [h0, h44, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h4, h44, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h47 | h47
                    · linarith only [h0, h47, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h3, h4, h47, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h50 | h50
            · rcases m.htr 0 3 4 (by decide) (by decide) with h51 | h51
              · rcases m.htr 0 3 5 (by decide) (by decide) with h52 | h52
                · rcases m.htr 0 4 5 (by decide) (by decide) with h53 | h53
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                    · linarith only [h0, h54, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h56 | h56
                      · linarith only [h1, h54, h56, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h58 | h58
                        · linarith only [h1, h54, h58, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h50, h58, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h61 | h61
                    · linarith only [h0, h4, h61, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h63 | h63
                      · linarith only [h1, h61, h63, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h65 | h65
                        · linarith only [h0, h65, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h50, h65, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h4, h50, h52, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h69 | h69
                · rcases m.htr 0 4 5 (by decide) (by decide) with h70 | h70
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
                    · linarith only [h0, h71, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
                      · linarith only [h1, h71, h73, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
                        · linarith only [h1, h71, h75, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h50, h75, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h4, h50, h51, h70, hlam]
                · linarith only [h4, h50, h69, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h80 | h80
              · rcases m.htr 0 3 5 (by decide) (by decide) with h81 | h81
                · rcases m.htr 0 4 5 (by decide) (by decide) with h82 | h82
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h83 | h83
                    · linarith only [h0, h4, h83, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
                      · linarith only [h0, h85, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h87 | h87
                        · linarith only [h1, h50, h83, h87, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
                          · linarith only [h1, h89, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h80, h89, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
                    · linarith only [h0, h92, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h94 | h94
                      · linarith only [h1, h92, h94, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h96 | h96
                        · linarith only [h0, h50, h96, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
                          · linarith only [h1, h98, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1, h80, h92, h98, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h101 | h101
                  · linarith only [h101, h80, h81, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
                    · linarith only [h0, h103, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h105 | h105
                      · linarith only [h0, h105, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
                        · linarith only [h1, h103, h107, h50, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h109 | h109
                          · linarith only [h1, h109, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h103, h109, h80, h81, hc12, hlam, hphi, ht23, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h112 | h112
                · rcases m.htr 0 4 5 (by decide) (by decide) with h113 | h113
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h114 | h114
                    · linarith only [h0, h114, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h116 | h116
                      · linarith only [h0, h116, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h118 | h118
                        · linarith only [h1, h114, h118, h50, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h120 | h120
                          · linarith only [h1, h120, h80, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h122 | h122
                            · linarith only [h120, h122, h2, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h112, h122, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h112, h113, h80, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h126 | h126
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
                    · linarith only [h0, h127, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
                      · linarith only [h0, h129, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h131 | h131
                        · linarith only [h0, h131, h50, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h133 | h133
                          · linarith only [h1, h133, h80, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h135 | h135
                            · linarith only [h1, h112, h135, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h137 | h137
                              · linarith only [h137, h2, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h126, h127, h133, h137, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h140 | h140
                    · linarith only [h0, h140, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h142 | h142
                      · linarith only [h0, h142, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h144 | h144
                        · linarith only [h1, h140, h144, h50, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h146 | h146
                          · linarith only [h1, h146, h80, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h148 | h148
                            · linarith only [h112, h146, h148, h2, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h150 | h150
                              · linarith only [h126, h150, h2, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h152 | h152
                                · linarith only [h0, h152, h4, h80, hc12, hlam, hphi, ht23, u3elo2]
                                · linarith only [h0, h152, h4, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h155 | h155
          · rcases m.htr 0 2 5 (by decide) (by decide) with h156 | h156
            · linarith only [h0, h156, h3, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h158 | h158
              · rcases m.htr 0 3 5 (by decide) (by decide) with h159 | h159
                · linarith only [h1, h159, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h161 | h161
                  · linarith only [h0, h158, h159, h161, h3, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h163 | h163
                    · linarith only [h0, h163, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h155, h163, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h166 | h166
                · linarith only [h1, h158, h166, h3, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h168 | h168
                  · linarith only [h168, h2, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
                    · linarith only [h0, h170, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h155, h170, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h173 | h173
            · linarith only [h0, h173, h3, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h175 | h175
              · rcases m.htr 0 3 5 (by decide) (by decide) with h176 | h176
                · linarith only [h1, h176, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h178 | h178
                  · linarith only [h1, h175, h176, h178, h3, hc13, hlam, hphi, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h180 | h180
                    · linarith only [h0, h180, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h182 | h182
                      · linarith only [h0, h182, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h184 | h184
                        · linarith only [h1, h173, h180, h184, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h186 | h186
                          · linarith only [h1, h186, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                          · linarith only [h175, h176, h186, hc13, hlam, hphi, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h189 | h189
                · linarith only [h0, h175, h189, h3, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h191 | h191
                  · linarith only [h191, h2, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h193 | h193
                    · linarith only [h0, h155, h193, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h195 | h195
                      · linarith only [h1, h193, h195, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h197 | h197
                        · linarith only [h1, h193, h197, h3, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h199 | h199
                          · linarith only [h1, h175, h199, h3, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h201 | h201
                            · linarith only [h189, h199, h2, h201, h3, hlam]
                            · linarith only [h193, h199, h2, h201, h3, hc12, hlam, hphi, ht23, u3elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h204 | h204
        · rcases m.htr 0 2 3 (by decide) (by decide) with h205 | h205
          · rcases m.htr 0 2 5 (by decide) (by decide) with h206 | h206
            · rcases m.htr 0 3 4 (by decide) (by decide) with h207 | h207
              · linarith only [h1, h2, h207, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h209 | h209
                · rcases m.htr 0 4 5 (by decide) (by decide) with h210 | h210
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h211 | h211
                    · linarith only [h0, h211, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h205, h211, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h2, h207, h209, h210, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h215 | h215
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h216 | h216
                    · linarith only [h0, h2, h216, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h2, h205, h216, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h2, h206, h215, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h220 | h220
              · linarith only [h1, h2, h220, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h222 | h222
                · linarith only [h205, h206, h220, h222, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h224 | h224
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h225 | h225
                    · linarith only [h0, h2, h225, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h205, h225, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h2, h204, h224, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h229 | h229
            · rcases m.htr 0 3 4 (by decide) (by decide) with h230 | h230
              · linarith only [h1, h2, h230, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h232 | h232
                · rcases m.htr 0 4 5 (by decide) (by decide) with h233 | h233
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h234 | h234
                    · linarith only [h0, h234, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h236 | h236
                      · linarith only [h0, h2, h236, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h238 | h238
                        · linarith only [h1, h2, h234, h238, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                        · linarith only [h205, h229, h230, h238, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1, h2, h205, h229, h230, h233, hc13, hlam, hphi, u3elo3]
                · linarith only [h205, h229, h232, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h243 | h243
              · linarith only [h1, h2, h243, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h245 | h245
                · rcases m.htr 0 4 5 (by decide) (by decide) with h246 | h246
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h247 | h247
                    · linarith only [h0, h247, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h249 | h249
                      · linarith only [h0, h2, h249, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h251 | h251
                        · linarith only [h1, h2, h229, h247, h251, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h253 | h253
                          · linarith only [h1, h2, h243, h253, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h1, h2, h253, hc13, hlam, hphi, u3elo3]
                  · linarith only [h1, h2, h245, h246, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h257 | h257
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h258 | h258
                    · linarith only [h0, h205, h258, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h260 | h260
                      · linarith only [h1, h258, h260, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h262 | h262
                        · linarith only [h0, h229, h262, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
                          · linarith only [h1, h2, h243, h264, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h1, h2, h258, h264, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h2, h204, h257, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h268 | h268
          · rcases m.htr 0 2 5 (by decide) (by decide) with h269 | h269
            · linarith only [h0, h204, h269, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h271 | h271
              · linarith only [h1, h2, h271, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h273 | h273
                · linarith only [h0, h204, h271, h273, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h275 | h275
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h276 | h276
                    · linarith only [h0, h204, h275, h276, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h204, h268, h275, h276, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h279 | h279
                    · linarith only [h0, h279, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h2, h268, h275, h279, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h282 | h282
            · linarith only [h0, h204, h282, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h284 | h284
              · linarith only [h1, h2, h284, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h286 | h286
                · linarith only [h0, h204, h284, h286, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h288 | h288
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h289 | h289
                    · linarith only [h0, h289, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h291 | h291
                      · linarith only [h0, h204, h288, h291, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h293 | h293
                        · linarith only [h1, h204, h282, h288, h289, h293, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h295 | h295
                          · linarith only [h1, h204, h284, h288, h295, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h0, h2, h295, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h298 | h298
                    · linarith only [h0, h268, h298, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h300 | h300
                      · linarith only [h1, h2, h288, h298, h300, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h302 | h302
                        · linarith only [h1, h2, h288, h298, h302, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h304 | h304
                          · linarith only [h1, h2, h288, h304, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                          · linarith only [h1, h2, h298, h304, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h308 | h308
    · rcases m.htr 0 1 4 (by decide) (by decide) with h309 | h309
      · rcases m.htr 0 1 5 (by decide) (by decide) with h310 | h310
        · rcases m.htr 0 2 3 (by decide) (by decide) with h311 | h311
          · rcases m.htr 0 2 5 (by decide) (by decide) with h312 | h312
            · rcases m.htr 0 3 4 (by decide) (by decide) with h313 | h313
              · rcases m.htr 0 3 5 (by decide) (by decide) with h314 | h314
                · rcases m.htr 0 4 5 (by decide) (by decide) with h315 | h315
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h316 | h316
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h317 | h317
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h318 | h318
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h319 | h319
                          · linarith only [h308, h319, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h313, h319, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h312, h318, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h309, h317, hlam]
                    · linarith only [h0, h316, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h325 | h325
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h326 | h326
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h327 | h327
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h328 | h328
                          · linarith only [h308, h328, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h313, h328, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h312, h327, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h309, h326, hlam]
                    · linarith only [h0, h325, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h334 | h334
                  · linarith only [h313, h314, h334, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h336 | h336
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h337 | h337
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h338 | h338
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h339 | h339
                          · linarith only [h308, h339, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h313, h339, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h308, h312, h336, h338, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h309, h337, hlam]
                    · linarith only [h0, h336, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h345 | h345
                · rcases m.htr 0 4 5 (by decide) (by decide) with h346 | h346
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h347 | h347
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h348 | h348
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h349 | h349
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h350 | h350
                          · linarith only [h308, h313, h350, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h352 | h352
                            · linarith only [h0, h309, h350, h352, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h345, h352, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h312, h349, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h309, h348, hlam]
                    · linarith only [h0, h347, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h313, h345, h346, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h359 | h359
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h360 | h360
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h361 | h361
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h362 | h362
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h363 | h363
                          · linarith only [h0, h308, h363, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h365 | h365
                            · linarith only [h0, h309, h345, h363, h365, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h367 | h367
                              · linarith only [h0, h309, h367, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h0, h309, h359, h367, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h0, h312, h362, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h309, h361, hlam]
                    · linarith only [h0, h360, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h373 | h373
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h374 | h374
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h375 | h375
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h376 | h376
                          · linarith only [h308, h313, h376, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h378 | h378
                            · linarith only [h308, h345, h378, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h380 | h380
                              · linarith only [h0, h308, h309, h313, h359, h373, h380, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h382 | h382
                                · linarith only [h308, h313, h373, h382, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h384 | h384
                                  · linarith only [h0, h308, h345, h373, h384, hc05, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h386 | h386
                                    · linarith only [h0, h310, h313, h359, h374, h380, h386, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h388 | h388
                                      · linarith only [h308, h313, h359, h373, h388, hc23, hlam, hphi, u3elo3]
                                      · rcases h5bigk with h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [hlam, p390_0]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h373, h376, h380, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p390_1, u0elo4]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h310, h386, hc24, hlam, hphi, ht0b, ht45, ht5b, p390_1, u0elo0]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h345, hlam, p390_0]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h359, hlam, p390_1]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h310, hlam, p390_0]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [hlam, p390_0]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h0, h310, h386, hc24, hlam, hphi, ht0b, ht45, ht5b, p390_1, u0elo1]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h378, hlam, p390_0]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h380, hlam, p390_1]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h312, hlam, p390_1]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h375, hlam, p390_1]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [hlam, p390_0]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h384, hlam, p390_1]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h386, hlam, p390_1]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h0, h310, h373, h376, h380, hc05, hc23, hlam, hphi, ht0b, ht5b, p390_1, u0elo1, u3elo4]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h373, h376, h380, hc23, hlam, hphi, p390_1, u3elo4]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h382, h386, hc23, hlam, hphi, p390_1, u3elo4]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [hlam, p390_0]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h388, hlam, p390_1]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h310, h373, h376, h380, hc23, hc45, hlam, hphi, ht34, p390_1]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h373, h376, h380, hc23, hc45, hlam, hphi, ht34, p390_1]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h382, h386, hc23, hc45, hlam, hphi, ht34, p390_1]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [h308, h345, h373, hc23, hc45, hlam, hphi, ht34, p390_1]
                                        · have p390_0 := h390c.1
                                          have p390_1 := h390c.2.1
                                          have p390_2 := h390c.2.2.1
                                          have p390_3 := h390c.2.2.2
                                          linarith only [hlam, p390_0]
                        · linarith only [h0, h312, h375, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h309, h374, hlam]
                    · linarith only [h0, h373, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h0, h310, h312, hlam]
          · linarith only [h0, h308, h311, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h421 | h421
          · rcases m.htr 0 2 5 (by decide) (by decide) with h422 | h422
            · rcases m.htr 0 3 4 (by decide) (by decide) with h423 | h423
              · rcases m.htr 0 3 5 (by decide) (by decide) with h424 | h424
                · linarith only [h308, h310, h424, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h426 | h426
                  · linarith only [h309, h310, h426, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h428 | h428
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h429 | h429
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h430 | h430
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h431 | h431
                          · linarith only [h308, h431, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h423, h424, h431, hc13, hlam, hphi, u3elo4]
                        · linarith only [h422, h430, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h309, h429, hlam]
                    · linarith only [h0, h428, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h437 | h437
                · linarith only [h309, h310, h423, h437, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h439 | h439
                  · linarith only [h309, h310, h439, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h441 | h441
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h442 | h442
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h443 | h443
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h444 | h444
                          · linarith only [h308, h423, h444, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h446 | h446
                            · linarith only [h308, h310, h437, h446, hlam]
                            · linarith only [h309, h310, h441, h444, h446, hc23, hlam, hphi, u3elo4]
                        · linarith only [h422, h443, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h309, h442, hlam]
                    · linarith only [h0, h441, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h452 | h452
              · rcases m.htr 0 3 5 (by decide) (by decide) with h453 | h453
                · linarith only [h0, h308, h422, h453, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h455 | h455
                  · linarith only [h0, h308, h422, h452, h455, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h457 | h457
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h458 | h458
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h459 | h459
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h460 | h460
                          · linarith only [h0, h308, h422, h460, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                          · linarith only [h452, h460, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h463 | h463
                          · linarith only [h0, h308, h422, h463, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                          · linarith only [h452, h453, h463, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h309, h458, hlam]
                    · linarith only [h0, h457, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h468 | h468
                · linarith only [h0, h309, h422, h452, h468, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h470 | h470
                  · linarith only [h0, h309, h422, h470, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h472 | h472
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h473 | h473
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h474 | h474
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h475 | h475
                          · linarith only [h308, h452, h475, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h477 | h477
                            · linarith only [h0, h308, h422, h468, h477, hlam]
                            · linarith only [h0, h309, h422, h472, h474, h475, h477, hc23, hlam, hphi, u3elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h480 | h480
                          · linarith only [h308, h452, h480, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h482 | h482
                            · linarith only [h308, h482, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h0, h309, h472, h474, h480, h482, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h309, h473, hlam]
                    · linarith only [h0, h309, h472, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
          · linarith only [h0, h308, h421, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h488 | h488
        · rcases m.htr 0 2 3 (by decide) (by decide) with h489 | h489
          · rcases m.htr 0 2 5 (by decide) (by decide) with h490 | h490
            · rcases m.htr 0 3 4 (by decide) (by decide) with h491 | h491
              · linarith only [h308, h309, h491, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h493 | h493
                · rcases m.htr 0 4 5 (by decide) (by decide) with h494 | h494
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h495 | h495
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h496 | h496
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h497 | h497
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h498 | h498
                          · linarith only [h308, h491, h498, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h308, h309, h498, hc13, hlam, hphi, u3elo3]
                        · linarith only [h308, h309, h490, h495, h496, h497, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h502 | h502
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h503 | h503
                          · linarith only [h308, h503, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h308, h495, h496, h503, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h308, h490, h495, h502, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h495, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h308, h309, h493, h494, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h509 | h509
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h510 | h510
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h511 | h511
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h512 | h512
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h513 | h513
                          · linarith only [h308, h513, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h308, h309, h513, hc13, hlam, hphi, u3elo3]
                        · linarith only [h308, h309, h490, h510, h511, h512, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h517 | h517
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h518 | h518
                          · linarith only [h308, h518, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h308, h511, h518, hc13, hlam, hphi, u3elo3]
                        · linarith only [h0, h308, h490, h510, h517, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h510, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h309, h488, h509, hlam]
            · linarith only [h0, h488, h490, hlam]
          · linarith only [h0, h308, h489, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h526 | h526
          · rcases m.htr 0 2 5 (by decide) (by decide) with h527 | h527
            · rcases m.htr 0 3 4 (by decide) (by decide) with h528 | h528
              · linarith only [h308, h309, h528, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h530 | h530
                · linarith only [h308, h488, h530, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h532 | h532
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h533 | h533
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h534 | h534
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h535 | h535
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h536 | h536
                          · linarith only [h308, h528, h536, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h308, h309, h533, h536, hc23, hlam, hphi, u3elo3]
                        · linarith only [h308, h309, h527, h533, h534, h535, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h540 | h540
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h541 | h541
                          · linarith only [h308, h488, h534, h540, h541, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h308, h488, h533, h534, h540, h541, hc23, hlam, hphi, u3elo3]
                        · linarith only [h527, h540, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h533, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h546 | h546
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h547 | h547
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h548 | h548
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h549 | h549
                          · linarith only [h308, h549, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h308, h309, h549, hc13, hlam, hphi, u3elo3]
                        · linarith only [h308, h309, h527, h546, h547, h548, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h553 | h553
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h554 | h554
                          · linarith only [h308, h488, h547, h553, h554, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h308, h488, h546, h547, h553, h554, hc23, hlam, hphi, u3elo3]
                        · linarith only [h527, h553, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h308, h546, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h559 | h559
              · linarith only [h308, h309, h559, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h561 | h561
                · linarith only [h526, h527, h559, h561, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h563 | h563
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h564 | h564
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h565 | h565
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h566 | h566
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h567 | h567
                          · linarith only [h0, h308, h559, h567, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h308, h309, h564, h567, hc23, hlam, hphi, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h570 | h570
                          · linarith only [h308, h570, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h308, h309, h570, hc13, hlam, hphi, u3elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h573 | h573
                        · linarith only [h0, h308, h527, h564, h565, h573, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h575 | h575
                          · linarith only [h308, h575, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h308, h564, h565, h575, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h564, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h579 | h579
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h580 | h580
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h581 | h581
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h582 | h582
                          · linarith only [h308, h582, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h308, h309, h582, hc13, hlam, hphi, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h585 | h585
                          · linarith only [h308, h585, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h308, h309, h585, hc13, hlam, hphi, u3elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h588 | h588
                        · linarith only [h0, h308, h527, h579, h580, h588, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h590 | h590
                          · linarith only [h308, h590, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h308, h580, h590, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h308, h579, hc13, hlam, hphi, u3elo2]
          · linarith only [h0, h308, h526, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h595 | h595
      · rcases m.htr 0 1 5 (by decide) (by decide) with h596 | h596
        · rcases m.htr 0 2 3 (by decide) (by decide) with h597 | h597
          · rcases m.htr 0 2 5 (by decide) (by decide) with h598 | h598
            · rcases m.htr 0 3 4 (by decide) (by decide) with h599 | h599
              · rcases m.htr 0 3 5 (by decide) (by decide) with h600 | h600
                · rcases m.htr 0 4 5 (by decide) (by decide) with h601 | h601
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h602 | h602
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h603 | h603
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h604 | h604
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h605 | h605
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h606 | h606
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h607 | h607
                              · linarith only [h308, h595, h607, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · linarith only [h308, h595, h601, h607, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h308, h606, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h308, h599, h605, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h308, h595, h598, h602, h603, h604, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h308, h595, h602, h603, hlam]
                    · linarith only [h597, h602, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h615 | h615
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h616 | h616
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h617 | h617
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h618 | h618
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h619 | h619
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h620 | h620
                              · linarith only [h595, h601, h620, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h622 | h622
                                · linarith only [h597, h622, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h597, h599, h622, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h308, h619, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h308, h595, h616, h618, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h308, h595, h598, h615, h616, h617, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h308, h595, h615, h616, hlam]
                    · linarith only [h0, h615, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h308, h596, h600, hlam]
              · linarith only [h308, h595, h599, hlam]
            · linarith only [h0, h596, h598, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h633 | h633
            · rcases m.htr 0 3 4 (by decide) (by decide) with h634 | h634
              · rcases m.htr 0 3 5 (by decide) (by decide) with h635 | h635
                · rcases m.htr 0 4 5 (by decide) (by decide) with h636 | h636
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h637 | h637
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h638 | h638
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h639 | h639
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h640 | h640
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h641 | h641
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h642 | h642
                              · linarith only [h0, h595, h597, h637, h642, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · linarith only [h0, h595, h597, h636, h637, h642, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h0, h597, h637, h641, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h0, h597, h634, h637, h640, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h595, h597, h637, h638, h639, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h597, h637, h638, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h595, h637, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h650 | h650
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h651 | h651
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h652 | h652
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h653 | h653
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h654 | h654
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h655 | h655
                              · linarith only [h595, h636, h655, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h657 | h657
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h658 | h658
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h659 | h659
                                    · linarith only [h595, h636, h651, h659, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h661 | h661
                                      · linarith only [h595, h636, h651, h657, h661, hlam]
                                      · rcases h5bigk with h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [hlam, p663_0]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h0, h596, h597, h650, h655, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p663_1, u3elo1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h0, h596, h597, h650, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p663_1, u3elo1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h0, h596, h597, h650, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p663_1, u3elo1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h636, hlam, p663_1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h596, hlam, p663_0]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [hlam, p663_0]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h0, h596, h597, h650, h658, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p663_1, u3elo1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h0, h596, h597, h650, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p663_1, u3elo1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h655, hlam, p663_1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h633, hlam, p663_1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h652, hlam, p663_1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [hlam, p663_0]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h597, h633, h650, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p663_1, u3elo1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h659, hlam, p663_1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h635, hlam, p663_1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h654, hlam, p663_1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h658, hlam, p663_0]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [hlam, p663_0]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h661, hlam, p663_1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h595, h636, h651, h657, hc34, hc45, hlam, hphi, p663_1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h651, h655, h657, hc34, hc45, hlam, hphi, p663_1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h657, h659, hc34, hc45, hlam, hphi, p663_1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [h661, hc34, hc45, hlam, hphi, p663_1]
                                        · have p663_0 := h663c.1
                                          have p663_1 := h663c.2.1
                                          have p663_2 := h663c.2.2.1
                                          have p663_3 := h663c.2.2.2
                                          linarith only [hlam, p663_0]
                                  · linarith only [h0, h597, h658, hc01, hlam, hphi, ht12, ht23, u3elo4]
                                · linarith only [h0, h596, h597, h651, h655, h657, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                            · linarith only [h308, h654, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h0, h595, h597, h650, h651, h653, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h0, h595, h597, h650, h651, h652, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h597, h650, h651, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h595, h650, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h308, h596, h635, hlam]
              · linarith only [h0, h595, h597, h634, hlam]
            · linarith only [h0, h596, h633, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h699 | h699
          · rcases m.htr 0 2 5 (by decide) (by decide) with h700 | h700
            · rcases m.htr 0 3 4 (by decide) (by decide) with h701 | h701
              · rcases m.htr 0 3 5 (by decide) (by decide) with h702 | h702
                · rcases m.htr 0 4 5 (by decide) (by decide) with h703 | h703
                  · linarith only [h595, h596, h703, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h705 | h705
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h706 | h706
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h707 | h707
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h708 | h708
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h709 | h709
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h710 | h710
                              · linarith only [h595, h703, h710, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h712 | h712
                                · linarith only [h699, h712, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h699, h701, h712, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h308, h595, h699, h702, h706, h709, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h308, h595, h706, h708, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h308, h595, h700, h705, h706, h707, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h308, h595, h705, h706, hlam]
                    · linarith only [h0, h595, h705, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h720 | h720
                  · linarith only [h595, h596, h720, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h722 | h722
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h723 | h723
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h724 | h724
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h725 | h725
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h726 | h726
                            · linarith only [h702, h726, hc03, hlam, hphi, u3elo1]
                            · linarith only [h308, h595, h723, h726, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h308, h595, h723, h725, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h308, h595, h700, h722, h723, h724, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h308, h595, h722, h723, hlam]
                    · linarith only [h699, h722, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h308, h595, h701, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h734 | h734
              · rcases m.htr 0 3 5 (by decide) (by decide) with h735 | h735
                · linarith only [h699, h700, h735, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h737 | h737
                  · linarith only [h308, h595, h699, h700, h735, h737, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h739 | h739
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h740 | h740
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h741 | h741
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h742 | h742
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h743 | h743
                            · linarith only [h308, h595, h735, h740, h743, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h308, h595, h740, h743, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h308, h595, h740, h742, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h747 | h747
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h748 | h748
                            · linarith only [h308, h595, h735, h740, h748, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h308, h595, h740, h748, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h308, h595, h740, h747, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h308, h595, h740, hc12, hlam, hphi, ht23, u3elo1]
                    · linarith only [h0, h739, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h308, h595, h734, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h755 | h755
            · rcases m.htr 0 3 4 (by decide) (by decide) with h756 | h756
              · rcases m.htr 0 3 5 (by decide) (by decide) with h757 | h757
                · rcases m.htr 0 4 5 (by decide) (by decide) with h758 | h758
                  · linarith only [h595, h596, h758, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h760 | h760
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h761 | h761
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h762 | h762
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h763 | h763
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h764 | h764
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h765 | h765
                              · linarith only [h595, h596, h699, h755, h758, h760, h765, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h767 | h767
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h768 | h768
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h769 | h769
                                    · linarith only [h595, h596, h699, h755, h760, h761, h765, h769, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h771 | h771
                                      · linarith only [h595, h596, h761, h765, h767, h771, hlam]
                                      · rcases h5bigk with h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [hlam, p773_0]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h596, hlam, p773_1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h699, h755, h760, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p773_1, u3elo1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h699, h755, h760, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p773_1, u3elo1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h758, hlam, p773_1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h596, hc01, hc15, hlam, hphi, p773_1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [hlam, p773_0]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h764, h768, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p773_1, u3elo1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h764, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p773_1, u3elo1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h765, hlam, p773_1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h755, hlam, p773_1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h762, hlam, p773_1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [hlam, p773_0]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h755, hc35, hlam, hphi, ht0b, ht5b, p773_1, u0elo1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h769, hlam, p773_1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h757, hlam, p773_1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h764, hlam, p773_1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h768, hlam, p773_0]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [hlam, p773_0]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h771, hlam, p773_1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h595, h596, h761, h767, hc34, hc45, hlam, hphi, p773_1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h595, h596, h761, h767, hc34, hc45, hlam, hphi, p773_1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h767, h769, hc34, hc45, hlam, hphi, p773_1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [h771, hc34, hc45, hlam, hphi, p773_1]
                                        · have p773_0 := h773c.1
                                          have p773_1 := h773c.2.1
                                          have p773_2 := h773c.2.2.1
                                          have p773_3 := h773c.2.2.2
                                          linarith only [hlam, p773_0]
                                  · linarith only [h699, h768, hc02, hlam, hphi, ht23, u3elo4]
                                · linarith only [h596, h699, h755, h767, hc01, hlam, hphi, ht12, ht23, u3elo3]
                            · linarith only [h757, h764, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h595, h596, h699, h755, h756, h760, h761, h763, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h595, h596, h699, h755, h760, h761, h762, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h596, h699, h755, h760, h761, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h595, h760, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h699, h755, h757, hlam]
              · linarith only [h0, h595, h699, h756, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h808 | h808
              · rcases m.htr 0 3 5 (by decide) (by decide) with h809 | h809
                · rcases m.htr 0 4 5 (by decide) (by decide) with h810 | h810
                  · linarith only [h0, h595, h755, h810, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h812 | h812
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h813 | h813
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h814 | h814
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h815 | h815
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h816 | h816
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h817 | h817
                              · linarith only [h0, h595, h755, h809, h810, h817, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h819 | h819
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h820 | h820
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h821 | h821
                                    · linarith only [h0, h595, h755, h813, h814, h817, h821, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h823 | h823
                                      · linarith only [h0, h595, h755, h813, h814, h817, h819, h823, hlam]
                                      · rcases h5bigk with h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [hlam, p825_0]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h596, hlam, p825_1]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h755, hlam, p825_0]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [hc35, hlam, hphi, ht0b, ht5b, p825_1, u0elo4]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h810, hlam, p825_1]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h816, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p825_1, u3elo1]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [hlam, p825_0]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h0, h755, h816, hc01, hlam, hphi, ht12, ht23, p825_1, u3elo1]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h816, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p825_1, u3elo1]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h817, hlam, p825_1]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h0, h595, h755, h813, h819, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p825_1]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h814, hlam, p825_1]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [hlam, p825_0]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h814, h816, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p825_1, u3elo1]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h821, hlam, p825_1]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h809, hlam, p825_1]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h816, hlam, p825_1]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h820, hlam, p825_0]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [hlam, p825_0]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h823, hlam, p825_1]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h0, h595, h755, h813, h819, hc34, hc45, hlam, hphi, p825_1]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h595, h596, h813, h819, hc34, hc45, hlam, hphi, p825_1]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h0, h595, h755, h813, h819, hc34, hc45, hlam, hphi, p825_1]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [h823, hc34, hc45, hlam, hphi, p825_1]
                                        · have p825_0 := h825c.1
                                          have p825_1 := h825c.2.1
                                          have p825_2 := h825c.2.2.1
                                          have p825_3 := h825c.2.2.2
                                          linarith only [hlam, p825_0]
                                  · linarith only [h0, h595, h699, h813, h819, h820, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · linarith only [h0, h699, h819, hc01, hlam, hphi, ht12, ht23, u3elo3]
                            · linarith only [h809, h816, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h0, h595, h699, h808, h812, h813, h815, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h0, h595, h699, h812, h813, h814, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h699, h812, h813, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h595, h812, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h858 | h858
                  · linarith only [h308, h595, h809, h858, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h860 | h860
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h861 | h861
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h862 | h862
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h863 | h863
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h864 | h864
                            · linarith only [h0, h699, h809, h864, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h308, h595, h861, h864, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h0, h595, h699, h860, h861, h863, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h0, h595, h699, h860, h861, h862, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h699, h860, h861, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h595, h860, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h0, h595, h699, h808, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h872 | h872
        · rcases m.htr 0 2 3 (by decide) (by decide) with h873 | h873
          · rcases m.htr 0 2 5 (by decide) (by decide) with h874 | h874
            · rcases m.htr 0 3 4 (by decide) (by decide) with h875 | h875
              · rcases m.htr 0 3 5 (by decide) (by decide) with h876 | h876
                · rcases m.htr 0 4 5 (by decide) (by decide) with h877 | h877
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h878 | h878
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h879 | h879
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h880 | h880
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h881 | h881
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h882 | h882
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h883 | h883
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h884 | h884
                                · linarith only [h873, h884, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h873, h875, h884, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · linarith only [h595, h872, h873, h875, h877, h880, h883, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h595, h872, h880, h881, h882, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                          · linarith only [h873, h875, h881, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h874, h880, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h891 | h891
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h892 | h892
                          · linarith only [h878, h879, h892, hlam]
                          · linarith only [h308, h872, h873, h875, h891, h892, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h308, h874, h878, h891, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h872, h878, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h595, h872, h877, hlam]
                · linarith only [h308, h872, h876, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h899 | h899
                · rcases m.htr 0 4 5 (by decide) (by decide) with h900 | h900
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h901 | h901
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h902 | h902
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h903 | h903
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h904 | h904
                          · linarith only [h308, h875, h904, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h308, h872, h903, h904, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h595, h874, h902, h903, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h908 | h908
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h909 | h909
                          · linarith only [h308, h872, h875, h908, h909, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h308, h872, h908, h909, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h0, h874, h908, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h872, h901, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h595, h872, h900, hlam]
                · linarith only [h308, h872, h899, hlam]
            · linarith only [h0, h872, h874, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h917 | h917
            · rcases m.htr 0 3 4 (by decide) (by decide) with h918 | h918
              · rcases m.htr 0 3 5 (by decide) (by decide) with h919 | h919
                · rcases m.htr 0 4 5 (by decide) (by decide) with h920 | h920
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h921 | h921
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h922 | h922
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h923 | h923
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h924 | h924
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h925 | h925
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h926 | h926
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h927 | h927
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h928 | h928
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h929 | h929
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h930 | h930
                                      · linarith only [h918, h930, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                      · linarith only [h920, h930, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                                    · linarith only [h0, h872, h873, h921, h926, h929, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                  · linarith only [h0, h873, h928, hc01, hlam, hphi, ht12, ht23, u3elo4]
                                · linarith only [h0, h872, h873, h926, h927, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h918, h920, h926, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h0, h873, h921, h925, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h0, h872, h873, h918, h921, h923, h924, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h0, h872, h873, h921, h923, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h872, h873, h921, h922, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h872, h921, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h595, h872, h920, hlam]
                · linarith only [h308, h872, h919, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h944 | h944
                · rcases m.htr 0 4 5 (by decide) (by decide) with h945 | h945
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h946 | h946
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h947 | h947
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h948 | h948
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h949 | h949
                          · linarith only [h0, h873, h918, h949, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h308, h872, h948, h949, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h0, h872, h873, h946, h948, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h872, h873, h946, h947, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h872, h946, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h0, h872, h873, h918, h945, hlam]
                · linarith only [h0, h872, h873, h944, hlam]
            · linarith only [h0, h872, h917, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h958 | h958
          · rcases m.htr 0 2 5 (by decide) (by decide) with h959 | h959
            · rcases m.htr 0 3 4 (by decide) (by decide) with h960 | h960
              · rcases m.htr 0 3 5 (by decide) (by decide) with h961 | h961
                · rcases m.htr 0 4 5 (by decide) (by decide) with h962 | h962
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h963 | h963
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h964 | h964
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h965 | h965
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h966 | h966
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h967 | h967
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h968 | h968
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h969 | h969
                                · linarith only [h958, h969, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h960, h969, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h595, h958, h960, h962, h968, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h308, h961, h967, hlam]
                          · linarith only [h308, h960, h966, hlam]
                        · linarith only [h0, h959, h965, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h976 | h976
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h977 | h977
                          · linarith only [h963, h964, h977, hlam]
                          · linarith only [h958, h960, h977, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h959, h976, hlam]
                    · linarith only [h0, h963, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h982 | h982
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h983 | h983
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h984 | h984
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h985 | h985
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h986 | h986
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h987 | h987
                              · linarith only [h595, h962, h985, h987, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h989 | h989
                                · linarith only [h958, h989, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h960, h989, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h958, h961, h986, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h308, h960, h961, h985, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                        · linarith only [h0, h959, h984, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h995 | h995
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h996 | h996
                          · linarith only [h982, h983, h996, hlam]
                          · linarith only [h960, h996, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h959, h995, hlam]
                    · linarith only [h0, h982, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1001 | h1001
                  · linarith only [h1001, h960, h961, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1003 | h1003
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1004 | h1004
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1005 | h1005
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1006 | h1006
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1007 | h1007
                            · linarith only [h1007, h961, hc03, hlam, hphi, u3elo1]
                            · linarith only [h1007, h308, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h1006, h308, h960, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1005, h959, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1012 | h1012
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1013 | h1013
                          · linarith only [h1003, h1004, h1013, hlam]
                          · linarith only [h1013, h960, h961, hc13, hlam, hphi, u3elo4]
                        · linarith only [h0, h1012, h959, hlam]
                    · linarith only [h0, h1003, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1018 | h1018
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1019 | h1019
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1020 | h1020
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1021 | h1021
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1022 | h1022
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1023 | h1023
                          · linarith only [h1023, h960, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1023, h308, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1022, h959, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1027 | h1027
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1028 | h1028
                          · linarith only [h1018, h1028, h960, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h1028, h308, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1027, h959, hlam]
                    · linarith only [h0, h1020, h958, hlam]
                  · linarith only [h1018, h1019, h960, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1034 | h1034
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1035 | h1035
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1036 | h1036
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1037 | h1037
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1038 | h1038
                          · linarith only [h1038, h960, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1038, h308, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1037, h959, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1042 | h1042
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1043 | h1043
                          · linarith only [h1043, h308, h960, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1043, h308, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1042, h959, hlam]
                    · linarith only [h0, h1035, h958, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1048 | h1048
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1049 | h1049
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1050 | h1050
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1051 | h1051
                          · linarith only [h1051, h308, h960, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1051, h308, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1050, h959, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1055 | h1055
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1056 | h1056
                          · linarith only [h1056, h308, h960, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1056, h308, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1055, h959, hlam]
                    · linarith only [h0, h1048, h958, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1061 | h1061
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1062 | h1062
                · linarith only [h1062, h958, h959, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1064 | h1064
                  · linarith only [h1061, h1064, h958, h959, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1066 | h1066
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1067 | h1067
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1068 | h1068
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1069 | h1069
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1070 | h1070
                            · linarith only [h1062, h1070, hc03, hlam, hphi, u3elo1]
                            · linarith only [h1070, h308, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h1061, h1069, h308, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1074 | h1074
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1075 | h1075
                            · linarith only [h1062, h1075, hc03, hlam, hphi, u3elo1]
                            · linarith only [h1075, h308, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h1061, h1074, h308, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1079 | h1079
                        · linarith only [h1067, h1079, h958, h959, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1081 | h1081
                          · linarith only [h1066, h1067, h1081, hlam]
                          · linarith only [h1061, h1062, h1081, hc13, hlam, hphi, u3elo4]
                    · linarith only [h1066, h958, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1085 | h1085
                · linarith only [h1061, h1085, h958, h959, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1087 | h1087
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1088 | h1088
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1089 | h1089
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1090 | h1090
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1091 | h1091
                          · linarith only [h1061, h1091, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1091, h308, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1094 | h1094
                          · linarith only [h1061, h1094, h308, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1094, h308, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1097 | h1097
                        · linarith only [h1089, h1097, h958, h959, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1099 | h1099
                          · linarith only [h1061, h1099, h308, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1099, h308, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h1088, h958, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1103 | h1103
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1104 | h1104
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1105 | h1105
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1106 | h1106
                          · linarith only [h1061, h1106, h308, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1106, h308, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1109 | h1109
                          · linarith only [h1061, h1109, h308, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1109, h308, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1112 | h1112
                        · linarith only [h1104, h1112, h958, h959, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1114 | h1114
                          · linarith only [h1061, h1114, h308, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1114, h308, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h1103, h958, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1118 | h1118
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1119 | h1119
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1120 | h1120
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1121 | h1121
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1122 | h1122
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1123 | h1123
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1124 | h1124
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1125 | h1125
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1126 | h1126
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1127 | h1127
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1128 | h1128
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1129 | h1129
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1130 | h1130
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1131 | h1131
                                      · linarith only [h1119, h1131, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                      · linarith only [h1119, h1121, h1131, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                    · linarith only [h1119, h1121, h1130, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                  · linarith only [h1129, h958, hc02, hlam, hphi, ht23, u3elo4]
                                · linarith only [h1128, h958, hc02, hlam, hphi, ht23, u3elo3]
                              · linarith only [h1119, h1121, h1127, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h1120, h1126, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1118, h1119, h1122, h1125, h958, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h1118, h1122, h1124, h958, hlam]
                      · linarith only [h1118, h1122, h1123, h958, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h1122, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1143 | h1143
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1144 | h1144
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1145 | h1145
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1146 | h1146
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1147 | h1147
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1148 | h1148
                              · linarith only [h1121, h1146, h1148, h595, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1150 | h1150
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1151 | h1151
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1152 | h1152
                                    · linarith only [h1144, h1148, h1152, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1154 | h1154
                                      · linarith only [h1118, h1143, h1148, h1150, h1152, h1154, h958, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                      · rcases h5bigk with h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [hlam, p1156_0]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h872, hlam, p1156_1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1152, hc24, hlam, hphi, ht0b, ht45, ht5b, p1156_1, u0elo4]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1118, h1143, h1154, h958, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1156_1, u3elo1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1121, hlam, p1156_1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1147, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1156_1, u3elo1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [hlam, p1156_0]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1147, h1152, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1156_1, u3elo1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1147, h1154, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1156_1, u3elo1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1148, hlam, p1156_1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1118, hlam, p1156_1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1145, hlam, p1156_1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [hlam, p1156_0]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1118, h1143, h1154, h958, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1156_1, u3elo1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1152, hlam, p1156_1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1120, hlam, p1156_1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1147, hlam, p1156_1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1151, hlam, p1156_0]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [hlam, p1156_0]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1154, hlam, p1156_1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1121, h595, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1156_1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h872, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1156_1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1151, h1154, hc34, hc45, hlam, hphi, p1156_1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [h1154, hc34, hc45, hlam, hphi, p1156_1]
                                        · have p1156_0 := h1156c.1
                                          have p1156_1 := h1156c.2.1
                                          have p1156_2 := h1156c.2.2.1
                                          have p1156_3 := h1156c.2.2.2
                                          linarith only [hlam, p1156_0]
                                  · linarith only [h1151, h958, hc02, hlam, hphi, ht23, u3elo4]
                                · linarith only [h1118, h1121, h1150, h595, h958, hc01, hlam, hphi, ht12, ht23, u3elo3]
                            · linarith only [h1120, h1147, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1118, h1119, h1121, h1143, h1146, h595, h958, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1118, h1143, h1145, h958, hlam]
                      · linarith only [h1118, h1143, h1144, h958, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h1143, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1118, h1120, h958, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1190 | h1190
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1191 | h1191
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1192 | h1192
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1193 | h1193
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1194 | h1194
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1195 | h1195
                          · linarith only [h1119, h1195, h958, hc02, hlam, hphi, ht23, u3elo1]
                          · linarith only [h1195, h308, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1118, h1192, h1194, h872, h958, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h1118, h1192, h1193, h872, h958, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1192, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1118, h1119, h1191, h958, hlam]
                · linarith only [h1118, h1190, h958, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1203 | h1203
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1204 | h1204
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1205 | h1205
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1206 | h1206
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1207 | h1207
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1208 | h1208
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1209 | h1209
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1210 | h1210
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1211 | h1211
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1212 | h1212
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1213 | h1213
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1214 | h1214
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1215 | h1215
                                      · linarith only [h1203, h1215, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                      · linarith only [h1205, h1215, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                                    · linarith only [h1203, h1205, h1214, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                  · linarith only [h1204, h1213, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h1212, h958, hc02, hlam, hphi, ht23, u3elo3]
                              · linarith only [h1203, h1205, h1211, h595, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h1203, h1204, h1206, h1210, h958, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                          · linarith only [h1203, h1206, h1209, h958, hlam]
                        · linarith only [h0, h1206, h1208, h958, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1206, h1207, h958, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1206, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1227 | h1227
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1228 | h1228
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1229 | h1229
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1230 | h1230
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1231 | h1231
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1232 | h1232
                              · linarith only [h1205, h1230, h1232, h595, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1234 | h1234
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1235 | h1235
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1236 | h1236
                                    · linarith only [h1228, h1232, h1236, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1238 | h1238
                                      · linarith only [h1203, h1232, h1238, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                                      · rcases h5bigk with h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [hlam, p1240_0]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h872, hlam, p1240_1]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h1118, hlam, p1240_0]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h1204, h1238, hc34, hlam, hphi, ht0b, ht45, ht5b, p1240_1, u0elo2]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h1205, hlam, p1240_1]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h1231, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1240_1, u3elo1]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [hlam, p1240_0]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h1231, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1240_1, u3elo1]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h1231, h1238, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1240_1, u3elo1]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h1232, hlam, p1240_1]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h0, h1118, hc01, hc25, hlam, hphi, ht12, p1240_1]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h1229, hlam, p1240_1]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [hlam, p1240_0]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h1229, h1231, h1238, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1240_1, u3elo1]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h1236, hlam, p1240_1]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h1204, hlam, p1240_1]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h1231, hlam, p1240_1]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h1235, hlam, p1240_0]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [hlam, p1240_0]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h1238, hlam, p1240_1]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h0, h1118, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1240_1]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h872, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1240_1]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h0, h1118, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1240_1]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [h1238, hc34, hc45, hlam, hphi, p1240_1]
                                        · have p1240_0 := h1240c.1
                                          have p1240_1 := h1240c.2.1
                                          have p1240_2 := h1240c.2.2.1
                                          have p1240_3 := h1240c.2.2.2
                                          linarith only [hlam, p1240_0]
                                  · linarith only [h0, h1235, h958, hc01, hlam, hphi, ht12, ht23, u3elo4]
                                · linarith only [h0, h1234, h958, hc01, hlam, hphi, ht12, ht23, u3elo3]
                            · linarith only [h1204, h1231, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h0, h1203, h1227, h1230, h958, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1227, h1229, h958, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1227, h1228, h958, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1227, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1273 | h1273
                  · linarith only [h1203, h1204, h1273, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1275 | h1275
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1276 | h1276
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1277 | h1277
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1278 | h1278
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1279 | h1279
                            · linarith only [h1204, h1279, hc03, hlam, hphi, u3elo1]
                            · linarith only [h1279, h308, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h0, h1203, h1275, h1278, h958, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1275, h1277, h958, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1275, h1276, h958, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1275, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1286 | h1286
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1287 | h1287
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1288 | h1288
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1289 | h1289
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1290 | h1290
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1291 | h1291
                          · linarith only [h1203, h1291, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1291, h308, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1288, h1290, h958, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1288, h1289, h958, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1288, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1203, h1286, h1287, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1298 | h1298
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1299 | h1299
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1300 | h1300
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1301 | h1301
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1302 | h1302
                          · linarith only [h1203, h1302, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1302, h308, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1299, h1301, h958, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1299, h1300, h958, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1299, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1308 | h1308
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1309 | h1309
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1310 | h1310
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1311 | h1311
                          · linarith only [h0, h1203, h1311, h958, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1311, h308, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1308, h1310, h958, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1308, h1309, h958, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1308, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 3462000 in
theorem n7l_sBT3_M_LI_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have h3ehi := hb3.1
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
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                      · linarith only [h1, h11, h8, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · linarith only [h0, h10, h11, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
                      · linarith only [h0, h14, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h16 | h16
                        · linarith only [h1, h16, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h1, h16, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h19, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                      · linarith only [h1, h19, h22, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · linarith only [h0, h21, h22, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
                      · linarith only [h0, h25, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
                        · linarith only [h1, h27, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h1, h27, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
              · linarith only [h5, h6, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h31 | h31
              · linarith only [h31, h5, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h33 | h33
                · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
                  · linarith only [h0, h34, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h37 | h37
                      · linarith only [h0, h37, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · linarith only [h0, h36, h37, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h40 | h40
                      · linarith only [h0, h40, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h42 | h42
                        · linarith only [h1, h42, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h44 | h44
                          · linarith only [h1, h31, h44, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
                            · linarith only [h2, h46, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                            · linarith only [h33, h42, h46, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
                  · linarith only [h0, h49, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h52 | h52
                      · linarith only [h0, h52, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · linarith only [h0, h4, h51, h52, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h55 | h55
                      · linarith only [h0, h55, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
                        · linarith only [h1, h5, h57, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h59 | h59
                          · linarith only [h1, h31, h59, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h61 | h61
                            · linarith only [h2, h61, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h64 | h64
                                · linarith only [h0, h1, h31, h4, h64, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                                · linarith only [h1, h5, h63, h64, hc35, hlam, hphi, u3ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h67 | h67
                                · linarith only [h63, h67, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
                                  · linarith only [h1, h33, h5, h63, h69, hc34, hlam, hphi, u3ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h71 | h71
                                    · linarith only [h1, h33, h5, h71, hc34, hlam, hphi, u3ehi1]
                                    · linarith only [h1, h5, h71, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h74 | h74
            · rcases m.htr 0 3 5 (by decide) (by decide) with h75 | h75
              · rcases m.htr 0 4 5 (by decide) (by decide) with h76 | h76
                · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
                  · linarith only [h0, h77, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h79 | h79
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                      · linarith only [h1, h4, h77, h80, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
                        · linarith only [h1, h82, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h74, h82, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h85 | h85
                      · linarith only [h0, h4, h85, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                        · linarith only [h1, h87, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h74, h87, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h90 | h90
                  · linarith only [h0, h90, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h92 | h92
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h93 | h93
                      · linarith only [h1, h4, h90, h93, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h95 | h95
                        · linarith only [h1, h95, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h1, h74, h95, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h98 | h98
                      · linarith only [h0, h4, h98, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h100 | h100
                        · linarith only [h1, h100, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h1, h100, h74, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
              · linarith only [h74, h75, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h104 | h104
              · linarith only [h104, h74, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h106 | h106
                · rcases m.htr 1 2 3 (by decide) (by decide) with h107 | h107
                  · linarith only [h0, h107, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h109 | h109
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h110 | h110
                      · linarith only [h107, h110, h4, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h112 | h112
                        · linarith only [h1, h112, h74, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · linarith only [h107, h109, h112, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h115 | h115
                      · linarith only [h0, h115, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h117 | h117
                        · linarith only [h1, h117, h74, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h119 | h119
                          · linarith only [h1, h104, h119, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h121 | h121
                            · linarith only [h121, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                            · linarith only [h106, h117, h121, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h124 | h124
                  · linarith only [h0, h124, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h126 | h126
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h127 | h127
                      · linarith only [h124, h127, h4, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h129 | h129
                        · linarith only [h1, h129, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h124, h126, h129, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h132 | h132
                      · linarith only [h0, h132, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h134 | h134
                        · linarith only [h1, h134, h74, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h136 | h136
                          · linarith only [h1, h104, h136, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h138 | h138
                            · linarith only [h106, h138, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h141 | h141
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h142 | h142
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h143 | h143
                                    · linarith only [h106, h134, h143, h2, hc34, hlam, hphi, u3ehi1]
                                    · linarith only [h140, h142, h143, h74, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                                  · linarith only [h140, h142, h74, hc45, hlam, hphi, ht34, u3ehi0]
                                · linarith only [h1, h140, h141, h74, hc35, hlam, hphi, u3ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h148 | h148
                                · linarith only [h140, h148, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h150 | h150
                                  · linarith only [h106, h134, h140, h150, h2, hc34, hlam, hphi, u3ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h152 | h152
                                    · linarith only [h124, h140, h150, h152, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h1, h152, h74, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h155 | h155
          · linarith only [h0, h155, h3, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h157 | h157
            · rcases m.htr 0 3 5 (by decide) (by decide) with h158 | h158
              · linarith only [h1, h158, h3, hlam]
              · linarith only [h157, h158, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h161 | h161
              · linarith only [h157, h161, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h163 | h163
                · linarith only [h163, h2, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
                  · linarith only [h0, h165, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h167 | h167
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h168 | h168
                      · linarith only [h1, h155, h165, h168, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h170 | h170
                        · linarith only [h1, h157, h168, h170, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h165, h167, h170, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h173 | h173
                      · linarith only [h1, h165, h173, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h175 | h175
                        · linarith only [h1, h157, h175, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h177 | h177
                          · linarith only [h161, h173, h175, h177, h2, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · linarith only [h175, h177, h2, h3, hc35, hlam, hphi, u3ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h180 | h180
        · rcases m.htr 0 2 5 (by decide) (by decide) with h181 | h181
          · rcases m.htr 0 3 4 (by decide) (by decide) with h182 | h182
            · linarith only [h1, h182, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h184 | h184
              · linarith only [h182, h184, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h186 | h186
                · rcases m.htr 1 2 3 (by decide) (by decide) with h187 | h187
                  · linarith only [h0, h187, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h189 | h189
                    · linarith only [h1, h187, h189, h2, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h191 | h191
                      · linarith only [h1, h187, h189, h191, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h181, h189, h191, h2, hc12, hc24, hlam, hphi]
                · linarith only [h1, h186, h2, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h195 | h195
            · linarith only [h1, h195, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h197 | h197
              · linarith only [h195, h197, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h199 | h199
                · rcases m.htr 1 2 3 (by decide) (by decide) with h200 | h200
                  · linarith only [h0, h200, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h202 | h202
                    · linarith only [h1, h2, h200, h202, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h204 | h204
                      · linarith only [h1, h181, h2, h200, h202, h204, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                        · linarith only [h1, h195, h2, h202, h206, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h1, h2, h206, hc34, hlam, hphi, u3ehi1]
                · linarith only [h1, h199, h2, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h210 | h210
          · linarith only [h0, h180, h210, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h212 | h212
            · linarith only [h1, h2, h212, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h214 | h214
              · linarith only [h212, h214, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h216 | h216
                · rcases m.htr 1 2 3 (by decide) (by decide) with h217 | h217
                  · linarith only [h0, h217, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h219 | h219
                    · linarith only [h1, h2, h217, h219, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h221 | h221
                      · linarith only [h1, h2, h210, h217, h219, h221, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h223 | h223
                        · linarith only [h1, h2, h212, h219, h223, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h1, h2, h223, hc34, hlam, hphi, u3ehi1]
                · linarith only [h1, h2, h216, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h227 | h227
      · rcases m.htr 0 1 5 (by decide) (by decide) with h228 | h228
        · rcases m.htr 0 2 5 (by decide) (by decide) with h229 | h229
          · rcases m.htr 0 3 4 (by decide) (by decide) with h230 | h230
            · rcases m.htr 0 3 5 (by decide) (by decide) with h231 | h231
              · rcases m.htr 0 4 5 (by decide) (by decide) with h232 | h232
                · rcases m.htr 1 2 3 (by decide) (by decide) with h233 | h233
                  · linarith only [h0, h233, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h235 | h235
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h236 | h236
                      · linarith only [h0, h1, h233, h236, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h229, h235, h236, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h239 | h239
                      · linarith only [h0, h1, h233, h239, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h229, h233, h239, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h242 | h242
                  · linarith only [h0, h242, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h244 | h244
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h245 | h245
                      · linarith only [h0, h1, h242, h245, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h229, h242, h245, hc12, hc23, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h248 | h248
                      · linarith only [h0, h1, h242, h248, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h229, h242, h248, hc12, hc23, hlam, hphi]
              · linarith only [h230, h231, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h227, h230, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h253 | h253
            · rcases m.htr 0 3 5 (by decide) (by decide) with h254 | h254
              · rcases m.htr 0 4 5 (by decide) (by decide) with h255 | h255
                · rcases m.htr 1 2 3 (by decide) (by decide) with h256 | h256
                  · linarith only [h0, h256, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h258 | h258
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h259 | h259
                      · linarith only [h0, h1, h229, h256, h259, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h261 | h261
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h262 | h262
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h263 | h263
                            · linarith only [h1, h228, h256, h258, h259, h263, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · linarith only [h1, h227, h255, h256, h261, h263, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1, h228, h259, h262, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h228, h258, h259, h261, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h268 | h268
                      · linarith only [h0, h229, h268, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h270 | h270
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h271 | h271
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h272 | h272
                            · linarith only [h227, h272, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                            · linarith only [h1, h227, h255, h256, h270, h272, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1, h227, h255, h271, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · linarith only [h1, h227, h255, h270, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h277 | h277
                  · linarith only [h0, h277, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h279 | h279
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h280 | h280
                      · linarith only [h0, h229, h280, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h282 | h282
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h283 | h283
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h284 | h284
                            · linarith only [h1, h228, h255, h277, h279, h280, h284, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h286 | h286
                              · linarith only [h1, h228, h277, h279, h280, h286, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h1, h228, h277, h280, h286, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h228, h279, h280, h282, h283, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1, h228, h280, h282, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h291 | h291
                      · linarith only [h0, h229, h291, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h293 | h293
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h294 | h294
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h295 | h295
                            · linarith only [h227, h255, h295, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h297 | h297
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h298 | h298
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h299 | h299
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h300 | h300
                                    · linarith only [h253, h255, h300, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                    · rcases h5bigk with h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [hlam, p302_0]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [hlam, hphi, ht0b, ht5b, p302_1, u0elo4, u5ehi1]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [h229, hlam, p302_0]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [h1, h228, h277, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p302_1, u3ehi4]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [h255, hlam, p302_1]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [h228, hlam, p302_0]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [hlam, p302_0]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [h291, hlam, p302_0]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [h1, h228, h277, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p302_1, u3ehi4]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [h295, hlam, p302_1]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        rcases p302_3 (m.d 0 5) (by simp) with h313 | h313
                                        · linarith only [h229, h313, hlam]
                                        · rcases p302_3 (m.d 1 5) (by simp) with h315 | h315
                                          · linarith only [h291, h315, hlam]
                                          · rcases p302_3 (m.d 2 5) (by simp) with h317 | h317
                                            · rcases p302_3 (m.d 3 5) (by simp) with h318 | h318
                                              · linarith only [h298, h318, hlam]
                                              · rcases p302_3 (m.d 4 5) (by simp) with h320 | h320
                                                · linarith only [h299, h320, hlam]
                                                · linarith only [h255, h320, hlam]
                                            · linarith only [h229, h317, hlam]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        rcases p302_3 (m.d 0 5) (by simp) with h324 | h324
                                        · linarith only [h229, h324, hlam]
                                        · linarith only [h228, h324, hlam]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [hlam, p302_0]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        rcases p302_3 (m.d 0 5) (by simp) with h328 | h328
                                        · linarith only [h229, h328, hlam]
                                        · linarith only [h254, h328, hlam]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [h227, h255, h293, h297, h299, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p302_1, u3ehi3]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [h254, hlam, p302_1]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [h294, hlam, p302_1]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [h298, hlam, p302_0]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [hlam, p302_0]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [h300, hlam, p302_1]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [h254, h300, hc45, hlam, hphi, ht34, p302_1, u3ehi3]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [h294, h300, hc45, hlam, hphi, ht34, p302_1, u3ehi3]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [h299, hlam, p302_0]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [h297, h299, h300, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p302_1, u3ehi3]
                                      · have p302_0 := h302c.1
                                        have p302_1 := h302c.2.1
                                        have p302_2 := h302c.2.2.1
                                        have p302_3 := h302c.2.2.2
                                        linarith only [hlam, p302_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h342 | h342
                                    · linarith only [h1, h227, h277, h293, h299, h342, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases h5bigk with h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [hlam, p344_0]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [hlam, hphi, ht0b, ht5b, p344_1, u0elo4, u5ehi1]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h229, hlam, p344_0]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h1, h228, h277, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p344_1, u5ehi3]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h255, hlam, p344_1]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h228, hlam, p344_0]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [hlam, p344_0]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h291, hlam, p344_0]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h1, h228, h277, h342, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p344_1, u3ehi3]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h295, hlam, p344_1]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h254, h299, h342, hc45, hlam, hphi, ht34, p344_1, u3ehi3]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h294, h299, h342, hc45, hlam, hphi, ht34, p344_1, u3ehi3]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [hlam, p344_0]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h299, h342, hc45, hlam, hphi, ht34, p344_1, u3ehi3]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h299, hlam, p344_1]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h254, hlam, p344_1]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h294, hlam, p344_1]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h298, hlam, p344_0]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [hlam, p344_0]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h342, hlam, p344_1]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h228, h294, h342, hc45, hlam, hphi, ht34, p344_1, u3ehi3]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h294, h342, hc45, hlam, hphi, ht34, p344_1, u3ehi3]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h0, h1, h228, h229, h277, h294, h342, hc12, hc23, hc45, hlam, hphi, ht34, p344_1, u3ehi3]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [h342, hc45, hlam, hphi, ht34, p344_1, u3ehi3]
                                      · have p344_0 := h344c.1
                                        have p344_1 := h344c.2.1
                                        have p344_2 := h344c.2.2.1
                                        have p344_3 := h344c.2.2.2
                                        linarith only [hlam, p344_0]
                                · linarith only [h1, h228, h277, h294, h298, hlam]
                              · linarith only [h1, h228, h277, h297, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · linarith only [h1, h227, h293, h294, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h0, h1, h293, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h253, h254, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h227, h253, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h376 | h376
          · linarith only [h0, h228, h376, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h378 | h378
            · rcases m.htr 0 3 5 (by decide) (by decide) with h379 | h379
              · rcases m.htr 0 4 5 (by decide) (by decide) with h380 | h380
                · linarith only [h227, h228, h380, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h382 | h382
                  · linarith only [h0, h228, h379, h382, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h384 | h384
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h385 | h385
                      · linarith only [h0, h1, h376, h382, h385, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h387 | h387
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h388 | h388
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h389 | h389
                            · linarith only [h0, h228, h380, h382, h384, h388, h389, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h228, h384, h389, hc24, hc45, hlam, hphi]
                          · linarith only [h379, h388, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                        · linarith only [h0, h1, h378, h387, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h394 | h394
                      · linarith only [h0, h376, h394, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h396 | h396
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h397 | h397
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h398 | h398
                            · linarith only [h227, h398, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                            · linarith only [h227, h228, h396, h398, hc45, hlam, hphi, ht34, u3ehi3]
                          · linarith only [h379, h397, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                        · linarith only [h1, h227, h384, h396, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h378, h379, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h227, h378, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h405 | h405
        · rcases m.htr 0 2 5 (by decide) (by decide) with h406 | h406
          · rcases m.htr 0 3 4 (by decide) (by decide) with h407 | h407
            · rcases m.htr 0 3 5 (by decide) (by decide) with h408 | h408
              · rcases m.htr 0 4 5 (by decide) (by decide) with h409 | h409
                · rcases m.htr 1 2 3 (by decide) (by decide) with h410 | h410
                  · linarith only [h0, h410, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h412 | h412
                    · linarith only [h0, h227, h412, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h414 | h414
                      · linarith only [h0, h1, h410, h414, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h406, h410, h414, hc12, hc23, hlam, hphi]
                · linarith only [h0, h227, h406, h409, hlam]
              · linarith only [h407, h408, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h419 | h419
              · linarith only [h407, h419, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h1, h406, h419, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h422 | h422
            · rcases m.htr 0 3 5 (by decide) (by decide) with h423 | h423
              · rcases m.htr 0 4 5 (by decide) (by decide) with h424 | h424
                · rcases m.htr 1 2 3 (by decide) (by decide) with h425 | h425
                  · linarith only [h0, h425, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h427 | h427
                    · linarith only [h0, h227, h427, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h429 | h429
                      · linarith only [h0, h1, h406, h425, h429, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h431 | h431
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h432 | h432
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h433 | h433
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h434 | h434
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h435 | h435
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h436 | h436
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h437 | h437
                                    · linarith only [h422, h437, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                    · linarith only [h422, h424, h437, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                                  · linarith only [h0, h227, h427, h436, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h227, h405, h425, h431, h432, h435, hlam]
                              · linarith only [h227, h405, h425, h431, h432, h434, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h227, h405, h432, h433, hc45, hlam, hphi, ht34, u3ehi4]
                          · linarith only [h227, h405, h429, h431, h432, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h405, h422, h431, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi1]
                · linarith only [h227, h405, h424, hlam]
              · linarith only [h422, h423, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h448 | h448
              · linarith only [h422, h448, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1, h405, h448, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h451 | h451
          · linarith only [h0, h405, h451, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h453 | h453
            · rcases m.htr 0 3 5 (by decide) (by decide) with h454 | h454
              · rcases m.htr 0 4 5 (by decide) (by decide) with h455 | h455
                · rcases m.htr 1 2 3 (by decide) (by decide) with h456 | h456
                  · linarith only [h0, h456, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h458 | h458
                    · linarith only [h0, h227, h458, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h460 | h460
                      · linarith only [h0, h1, h451, h456, h460, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h462 | h462
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h463 | h463
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h464 | h464
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h465 | h465
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h466 | h466
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h467 | h467
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h468 | h468
                                    · linarith only [h453, h468, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                    · linarith only [h453, h455, h468, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                                  · linarith only [h405, h453, h455, h458, h464, h467, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h1, h454, h456, h466, hlam]
                              · linarith only [h1, h454, h456, h465, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h227, h455, h464, hlam]
                          · linarith only [h1, h454, h463, hlam]
                        · linarith only [h1, h453, h462, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h477 | h477
                  · linarith only [h0, h477, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h479 | h479
                    · linarith only [h0, h227, h455, h479, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h481 | h481
                      · linarith only [h0, h227, h455, h481, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h483 | h483
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h484 | h484
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h485 | h485
                            · linarith only [h0, h227, h455, h477, h483, h485, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h227, h485, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h0, h1, h484, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h454, h483, hc34, hlam, hphi, u3ehi4]
              · linarith only [h453, h454, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h491 | h491
              · linarith only [h453, h491, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h493 | h493
                · rcases m.htr 1 2 3 (by decide) (by decide) with h494 | h494
                  · linarith only [h0, h494, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h496 | h496
                    · linarith only [h0, h227, h496, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h498 | h498
                      · linarith only [h0, h1, h453, h498, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h500 | h500
                        · linarith only [h0, h1, h453, h494, h500, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h500, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h503 | h503
                  · linarith only [h0, h503, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h505 | h505
                    · linarith only [h0, h1, h453, h493, h505, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h507 | h507
                      · linarith only [h0, h1, h453, h493, h507, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h509 | h509
                        · linarith only [h0, h1, h453, h503, h509, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h509, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h512 | h512
    · rcases m.htr 0 1 4 (by decide) (by decide) with h513 | h513
      · rcases m.htr 0 1 5 (by decide) (by decide) with h514 | h514
        · rcases m.htr 0 2 5 (by decide) (by decide) with h515 | h515
          · rcases m.htr 0 3 4 (by decide) (by decide) with h516 | h516
            · rcases m.htr 0 3 5 (by decide) (by decide) with h517 | h517
              · rcases m.htr 0 4 5 (by decide) (by decide) with h518 | h518
                · rcases m.htr 1 2 3 (by decide) (by decide) with h519 | h519
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h520 | h520
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h521 | h521
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h522 | h522
                        · linarith only [h512, h522, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h516, h522, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h0, h514, h521, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h514, h520, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h512, h516, h519, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h528 | h528
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h529 | h529
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h530 | h530
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h531 | h531
                        · linarith only [h512, h531, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h516, h531, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h0, h512, h516, h530, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h512, h516, h529, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h512, h516, h528, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h516, h517, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h538 | h538
              · linarith only [h516, h538, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h540 | h540
                · rcases m.htr 1 2 3 (by decide) (by decide) with h541 | h541
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h542 | h542
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h543 | h543
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h544 | h544
                        · linarith only [h512, h516, h544, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h546 | h546
                          · linarith only [h0, h512, h546, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h548 | h548
                            · linarith only [h0, h513, h548, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · linarith only [h0, h513, h540, h544, h548, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h0, h514, h543, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h512, h541, h542, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h512, h541, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h554 | h554
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h555 | h555
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h556 | h556
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h557 | h557
                        · linarith only [h512, h557, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h559 | h559
                          · linarith only [h0, h513, h557, h559, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h561 | h561
                            · linarith only [h0, h513, h516, h540, h561, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h563 | h563
                              · linarith only [h512, h516, h554, h563, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h565 | h565
                                · linarith only [h512, h516, h554, h565, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h567 | h567
                                  · linarith only [h0, h514, h516, h540, h555, h561, h567, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h569 | h569
                                    · linarith only [h512, h516, h540, h554, h569, hc34, hlam, hphi, u3ehi2]
                                    · linarith only [h512, h516, h554, h569, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h0, h514, h556, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h512, h554, h555, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h512, h554, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h514, h515, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h576 | h576
          · rcases m.htr 0 3 4 (by decide) (by decide) with h577 | h577
            · rcases m.htr 0 3 5 (by decide) (by decide) with h578 | h578
              · linarith only [h512, h514, h578, hlam]
              · linarith only [h577, h578, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h581 | h581
              · linarith only [h577, h581, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h583 | h583
                · linarith only [h513, h514, h583, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h585 | h585
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h586 | h586
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h587 | h587
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h588 | h588
                        · linarith only [h512, h588, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h590 | h590
                          · linarith only [h513, h514, h576, h581, h588, h590, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                          · linarith only [h512, h514, h585, h590, hc35, hlam, hphi, u3ehi2]
                      · linarith only [h0, h512, h576, h585, h587, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                    · linarith only [h0, h512, h585, h586, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h512, h585, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h596 | h596
            · rcases m.htr 0 3 5 (by decide) (by decide) with h597 | h597
              · linarith only [h512, h514, h597, hlam]
              · linarith only [h596, h597, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h600 | h600
              · linarith only [h596, h600, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h602 | h602
                · linarith only [h0, h513, h576, h602, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h604 | h604
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h605 | h605
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h606 | h606
                      · linarith only [h0, h512, h576, h604, h606, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h512, h604, h606, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h512, h604, h605, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h512, h604, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h611 | h611
        · rcases m.htr 0 2 5 (by decide) (by decide) with h612 | h612
          · rcases m.htr 0 3 4 (by decide) (by decide) with h613 | h613
            · linarith only [h512, h513, h613, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h615 | h615
              · linarith only [h613, h615, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h617 | h617
                · rcases m.htr 1 2 3 (by decide) (by decide) with h618 | h618
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h619 | h619
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h620 | h620
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h621 | h621
                        · linarith only [h512, h613, h621, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · linarith only [h512, h513, h618, h621, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h512, h513, h618, h619, h620, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h512, h618, h619, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h512, h618, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h512, h513, h617, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h611, h612, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h629 | h629
          · rcases m.htr 0 3 4 (by decide) (by decide) with h630 | h630
            · linarith only [h512, h513, h630, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h632 | h632
              · linarith only [h630, h632, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h634 | h634
                · rcases m.htr 1 2 3 (by decide) (by decide) with h635 | h635
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h636 | h636
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h637 | h637
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h638 | h638
                        · linarith only [h512, h630, h638, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · linarith only [h512, h513, h635, h638, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h629, h636, h637, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h0, h512, h635, h636, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h512, h635, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h512, h513, h634, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h645 | h645
            · linarith only [h512, h513, h645, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h647 | h647
              · linarith only [h645, h647, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h649 | h649
                · rcases m.htr 1 2 3 (by decide) (by decide) with h650 | h650
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h651 | h651
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h652 | h652
                      · linarith only [h0, h512, h629, h650, h652, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h512, h650, h652, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h512, h650, h651, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h512, h650, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h512, h513, h649, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h658 | h658
      · rcases m.htr 0 1 5 (by decide) (by decide) with h659 | h659
        · rcases m.htr 0 2 5 (by decide) (by decide) with h660 | h660
          · rcases m.htr 0 3 4 (by decide) (by decide) with h661 | h661
            · rcases m.htr 0 3 5 (by decide) (by decide) with h662 | h662
              · rcases m.htr 0 4 5 (by decide) (by decide) with h663 | h663
                · rcases m.htr 1 2 3 (by decide) (by decide) with h664 | h664
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h665 | h665
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h666 | h666
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h667 | h667
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h668 | h668
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h669 | h669
                            · linarith only [h658, h669, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                            · linarith only [h663, h667, h669, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                          · linarith only [h512, h658, h667, h668, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h512, h658, h663, h667, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h512, h658, h663, h664, h666, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h512, h658, h663, h664, h665, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h658, h663, h664, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h677 | h677
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h678 | h678
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h679 | h679
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h680 | h680
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h681 | h681
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h682 | h682
                            · linarith only [h658, h663, h682, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h684 | h684
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h685 | h685
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h686 | h686
                                  · linarith only [h658, h663, h678, h686, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h688 | h688
                                    · linarith only [h658, h663, h678, h684, h688, hlam]
                                    · rcases h5bigk with h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [hlam, p690_0]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h512, h659, h677, h678, h682, h684, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p690_1, u3ehi3]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h512, h659, h677, hc12, hlam, hphi, ht01, ht0b, ht5b, p690_1, u5ehi2]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h512, h659, h677, h688, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p690_1, u3ehi3]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h663, hlam, p690_1]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h659, hlam, p690_0]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [hlam, p690_0]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h512, h659, h677, hc12, hlam, hphi, ht01, ht0b, ht5b, p690_1, u5ehi2]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h512, h659, h677, h688, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p690_1, u3ehi3]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h682, hlam, p690_1]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h660, hlam, p690_1]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h679, hlam, p690_1]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [hlam, p690_0]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h660, h688, hlam, hphi, ht0b, ht34, ht45, ht5b, p690_1, u0elo1, u3ehi3]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h686, hlam, p690_1]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h662, hlam, p690_1]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h681, hlam, p690_1]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h685, hlam, p690_0]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [hlam, p690_0]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h688, hlam, p690_1]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h662, h688, hc45, hlam, hphi, ht34, p690_1, u3ehi3]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h681, h688, hc45, hlam, hphi, ht34, p690_1, u3ehi3]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h685, h688, hc45, hlam, hphi, ht34, p690_1, u3ehi3]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [h688, hc45, hlam, hphi, ht34, p690_1, u3ehi3]
                                      · have p690_0 := h690c.1
                                        have p690_1 := h690c.2.1
                                        have p690_2 := h690c.2.2.1
                                        have p690_3 := h690c.2.2.2
                                        linarith only [hlam, p690_0]
                                · linarith only [h662, h685, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                              · linarith only [h661, h684, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                          · linarith only [h512, h659, h681, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h512, h659, h661, h679, h680, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
                      · linarith only [h512, h659, h677, h679, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h512, h659, h677, h678, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h659, h677, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h661, h662, hc35, hlam, hphi, u3ehi3]
            · linarith only [h512, h658, h661, hlam]
          · linarith only [h0, h659, h660, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h726 | h726
          · rcases m.htr 0 3 4 (by decide) (by decide) with h727 | h727
            · rcases m.htr 0 3 5 (by decide) (by decide) with h728 | h728
              · rcases m.htr 0 4 5 (by decide) (by decide) with h729 | h729
                · linarith only [h658, h659, h729, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h731 | h731
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h732 | h732
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h733 | h733
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h734 | h734
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h735 | h735
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h736 | h736
                            · linarith only [h658, h729, h736, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h658, h659, h734, h736, hc45, hlam, hphi, ht34, u3ehi3]
                          · linarith only [h728, h735, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                        · linarith only [h512, h728, h734, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h512, h726, h731, h733, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                    · linarith only [h0, h658, h732, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h743 | h743
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h744 | h744
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h745 | h745
                        · linarith only [h658, h659, h731, h744, h745, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h659, h727, h731, h744, h745, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h658, h726, h727, h744, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                    · linarith only [h0, h658, h743, hlam]
              · linarith only [h727, h728, hc35, hlam, hphi, u3ehi3]
            · linarith only [h512, h658, h727, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h752 | h752
            · rcases m.htr 0 3 5 (by decide) (by decide) with h753 | h753
              · rcases m.htr 0 4 5 (by decide) (by decide) with h754 | h754
                · linarith only [h658, h659, h754, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h756 | h756
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h757 | h757
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h758 | h758
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h759 | h759
                        · linarith only [h0, h658, h726, h758, h759, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h512, h752, h759, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h762 | h762
                        · linarith only [h512, h658, h756, h758, h762, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h512, h658, h752, h762, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h512, h658, h756, h757, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h766 | h766
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h767 | h767
                      · linarith only [h726, h756, h767, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h769 | h769
                        · linarith only [h0, h658, h756, h769, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h512, h658, h752, h769, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h0, h658, h766, hlam]
              · linarith only [h752, h753, hc35, hlam, hphi, u3ehi3]
            · linarith only [h512, h658, h752, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h775 | h775
        · rcases m.htr 0 2 5 (by decide) (by decide) with h776 | h776
          · rcases m.htr 0 3 4 (by decide) (by decide) with h777 | h777
            · rcases m.htr 0 3 5 (by decide) (by decide) with h778 | h778
              · rcases m.htr 0 4 5 (by decide) (by decide) with h779 | h779
                · rcases m.htr 1 2 3 (by decide) (by decide) with h780 | h780
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h781 | h781
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h782 | h782
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h783 | h783
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h784 | h784
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h785 | h785
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h786 | h786
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h787 | h787
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h788 | h788
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h789 | h789
                                    · linarith only [h777, h789, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                    · linarith only [h779, h789, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                                  · linarith only [h775, h785, h786, h788, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                                · linarith only [h778, h787, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                              · linarith only [h777, h786, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                            · linarith only [h658, h775, h785, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                          · linarith only [h658, h775, h782, h783, h784, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h777, h783, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h0, h775, h782, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h512, h775, h780, h781, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h775, h780, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h658, h775, h779, hlam]
              · linarith only [h777, h778, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h803 | h803
              · linarith only [h777, h803, hc34, hlam, hphi, u3ehi4]
              · linarith only [h512, h775, h803, hlam]
          · linarith only [h0, h775, h776, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h807 | h807
          · rcases m.htr 0 3 4 (by decide) (by decide) with h808 | h808
            · rcases m.htr 0 3 5 (by decide) (by decide) with h809 | h809
              · rcases m.htr 0 4 5 (by decide) (by decide) with h810 | h810
                · rcases m.htr 1 2 3 (by decide) (by decide) with h811 | h811
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h812 | h812
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h813 | h813
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h814 | h814
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h815 | h815
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h816 | h816
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h817 | h817
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h818 | h818
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h819 | h819
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h820 | h820
                                    · linarith only [h808, h820, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                    · linarith only [h810, h820, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                                  · linarith only [h808, h810, h817, h819, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                                · linarith only [h809, h818, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                              · linarith only [h808, h817, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                            · linarith only [h658, h808, h810, h816, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h809, h815, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                        · linarith only [h512, h808, h814, hlam]
                      · linarith only [h0, h807, h813, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h830 | h830
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h831 | h831
                        · linarith only [h811, h812, h831, hlam]
                        · linarith only [h512, h808, h831, hlam]
                      · linarith only [h0, h807, h830, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h835 | h835
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h836 | h836
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h837 | h837
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h838 | h838
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h839 | h839
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h840 | h840
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h841 | h841
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h842 | h842
                                  · linarith only [h811, h835, h842, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                  · linarith only [h808, h810, h840, h842, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                                · linarith only [h658, h810, h811, h835, h841, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                              · linarith only [h658, h810, h811, h835, h840, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · linarith only [h658, h810, h839, hlam]
                          · linarith only [h512, h809, h838, hlam]
                        · linarith only [h512, h808, h837, hlam]
                      · linarith only [h0, h807, h836, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h851 | h851
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h852 | h852
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h853 | h853
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h854 | h854
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h855 | h855
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h856 | h856
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h857 | h857
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h858 | h858
                                    · linarith only [h808, h858, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                    · linarith only [h810, h858, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                                  · linarith only [h0, h807, h808, h810, h835, h856, h857, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi4]
                                · linarith only [h0, h807, h835, h855, h856, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                              · linarith only [h808, h855, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                            · linarith only [h658, h810, h854, hlam]
                          · linarith only [h512, h809, h853, hlam]
                        · linarith only [h512, h808, h852, hlam]
                      · linarith only [h0, h807, h851, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h868 | h868
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h869 | h869
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h870 | h870
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h871 | h871
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h872 | h872
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h873 | h873
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h874 | h874
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h875 | h875
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h876 | h876
                                  · linarith only [h808, h810, h868, h874, h876, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h878 | h878
                                    · linarith only [h808, h810, h878, hlam]
                                    · rcases h5bigk with h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [hlam, p880_0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h775, hlam, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h874, h876, hlam, hphi, ht0b, ht34, ht45, ht5b, p880_1, u0elo4, u3ehi3]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h810, h871, h873, h878, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p880_1, u3ehi3]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h810, hlam, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        rcases p880_3 (m.d 0 5) (by simp) with h886 | h886
                                        · linarith only [h775, h886, hlam]
                                        · rcases p880_3 (m.d 1 5) (by simp) with h888 | h888
                                          · rcases p880_3 (m.d 2 5) (by simp) with h889 | h889
                                            · linarith only [h870, h889, hlam]
                                            · rcases p880_3 (m.d 3 5) (by simp) with h891 | h891
                                              · linarith only [h872, h891, hlam]
                                              · rcases p880_3 (m.d 4 5) (by simp) with h893 | h893
                                                · linarith only [h873, h893, hlam]
                                                · linarith only [h810, h893, hlam]
                                          · linarith only [h775, h888, hlam]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [hlam, p880_0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        rcases p880_3 (m.d 0 5) (by simp) with h898 | h898
                                        · linarith only [h775, h898, hlam]
                                        · linarith only [h807, h898, hlam]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        rcases p880_3 (m.d 0 5) (by simp) with h901 | h901
                                        · linarith only [h775, h901, hlam]
                                        · linarith only [h809, h901, hlam]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h808, h810, h868, h871, h873, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p880_1, u3ehi3]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h807, hlam, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h870, hlam, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [hlam, p880_0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h807, h878, hlam, hphi, ht0b, ht34, ht45, ht5b, p880_1, u0elo1, u3ehi3]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h876, hlam, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h809, hlam, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h872, hlam, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h875, hlam, p880_0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [hlam, p880_0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h878, hlam, p880_1]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h809, h878, hc45, hlam, hphi, ht34, p880_1, u3ehi3]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h873, hlam, p880_0]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h868, h871, h873, h875, h878, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p880_1, u3ehi3]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [h868, h871, h873, h878, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p880_1, u3ehi3]
                                      · have p880_0 := h880c.1
                                        have p880_1 := h880c.2.1
                                        have p880_2 := h880c.2.2.1
                                        have p880_3 := h880c.2.2.2
                                        linarith only [hlam, p880_0]
                                · linarith only [h809, h875, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                              · linarith only [h808, h874, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h922 | h922
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h923 | h923
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h924 | h924
                                  · linarith only [h658, h873, h924, hc01, hc24, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h926 | h926
                                    · linarith only [h658, h808, h873, h926, hlam]
                                    · rcases h5bigk with h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [hlam, p928_0]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h775, hlam, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [hlam, hphi, ht0b, ht5b, p928_1, u0elo4, u5ehi2]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p928_1, u0elo4, u3ehi4]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h810, hlam, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h807, h873, h922, h924, hc45, hlam, hphi, ht34, p928_1, u3ehi3]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [hlam, p928_0]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h873, h922, h924, hc45, hlam, hphi, ht34, p928_1, u3ehi3]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h873, hc45, hlam, hphi, ht34, p928_1, u3ehi4]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h873, hlam, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h807, hlam, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h870, hlam, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [hlam, p928_0]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h807, hlam, hphi, ht0b, ht34, ht45, ht5b, p928_1, u0elo1, u3ehi4]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h924, hlam, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h809, hlam, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h872, hlam, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h923, hlam, p928_0]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [hlam, p928_0]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h926, hlam, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h809, hc45, hlam, hphi, ht34, p928_1, u3ehi4]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h775, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h923, hc45, hlam, hphi, ht34, p928_1, u3ehi4]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [hc45, hlam, hphi, ht34, p928_1, u3ehi4]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [hlam, p928_0]
                                · linarith only [h809, h923, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                              · linarith only [h808, h922, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                          · linarith only [h512, h808, h809, h872, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4, u3ehi3]
                        · linarith only [h512, h808, h871, hlam]
                      · linarith only [h0, h807, h870, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h959 | h959
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h960 | h960
                        · linarith only [h868, h869, h960, hlam]
                        · linarith only [h512, h808, h960, hlam]
                      · linarith only [h0, h807, h959, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h964 | h964
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h965 | h965
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h966 | h966
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h967 | h967
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h968 | h968
                            · linarith only [h658, h810, h868, h964, h968, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h970 | h970
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h971 | h971
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h972 | h972
                                  · linarith only [h868, h964, h968, h972, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h974 | h974
                                    · linarith only [h658, h808, h968, h974, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                    · rcases h5bigk with h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [hlam, p976_0]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h775, hlam, p976_1]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h0, h807, h868, h970, h972, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p976_1, u3ehi3]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h0, h807, h868, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p976_1, u5ehi3]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h810, hlam, p976_1]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h868, h965, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p976_1, u5ehi0]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [hlam, p976_0]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h868, h965, h970, h972, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p976_1, u3ehi3]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h868, h965, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p976_1, u3ehi4]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h968, hlam, p976_1]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h807, hlam, p976_1]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h965, hlam, p976_1]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [hlam, p976_0]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h807, hlam, hphi, ht0b, ht34, ht45, ht5b, p976_1, u0elo4, u3ehi4]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h972, hlam, p976_1]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h809, hlam, p976_1]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h967, hlam, p976_1]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h971, hlam, p976_0]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [hlam, p976_0]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h974, hlam, p976_1]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h809, hc45, hlam, hphi, ht34, p976_1, u3ehi4]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h775, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p976_1]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [h971, hc45, hlam, hphi, ht34, p976_1, u3ehi4]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [hc45, hlam, hphi, ht34, p976_1, u3ehi4]
                                      · have p976_0 := h976c.1
                                        have p976_1 := h976c.2.1
                                        have p976_2 := h976c.2.2.1
                                        have p976_3 := h976c.2.2.2
                                        linarith only [hlam, p976_0]
                                · linarith only [h0, h807, h868, h971, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                              · linarith only [h0, h807, h808, h868, h970, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
                          · linarith only [h512, h808, h967, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h512, h808, h966, hlam]
                      · linarith only [h0, h807, h965, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1007 | h1007
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1008 | h1008
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1009 | h1009
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1010 | h1010
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1011 | h1011
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1012 | h1012
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1013 | h1013
                                  · linarith only [h1013, h807, h810, hlam]
                                  · linarith only [h0, h1013, h807, h964, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                                · linarith only [h1007, h1010, h1011, h1012, h808, h810, h964, hc35, hlam, hphi, u3ehi3]
                              · linarith only [h1008, h1010, h1011, h808, h810, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h1007, h1010, h964, hlam]
                          · linarith only [h1009, h809, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                        · linarith only [h1008, h512, h807, h808, h809, h810, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                      · linarith only [h0, h1007, h807, hlam]
              · linarith only [h808, h809, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1023 | h1023
              · linarith only [h1023, h808, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1025 | h1025
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1026 | h1026
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1027 | h1027
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1028 | h1028
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1029 | h1029
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1030 | h1030
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1031 | h1031
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1032 | h1032
                              · linarith only [h1026, h1032, h808, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1034 | h1034
                                · linarith only [h1023, h1029, h1032, h1034, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1036 | h1036
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1037 | h1037
                                    · rcases h5bigk with h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [hlam, p1038_0]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [h775, hlam, p1038_1]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [h1034, hlam, hphi, ht0b, ht34, ht45, ht5b, p1038_1, u0elo4, u3ehi2]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [h1023, hlam, p1038_0]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [h1025, hlam, hphi, ht0b, ht5b, p1038_1, u0elo3, u5ehi4]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        rcases p1038_3 (m.d 0 5) (by simp) with h1044 | h1044
                                        · linarith only [h1044, h775, hlam]
                                        · rcases p1038_3 (m.d 1 5) (by simp) with h1046 | h1046
                                          · rcases p1038_3 (m.d 2 5) (by simp) with h1047 | h1047
                                            · linarith only [h1028, h1047, hlam]
                                            · rcases p1038_3 (m.d 3 5) (by simp) with h1049 | h1049
                                              · linarith only [h1030, h1049, hlam]
                                              · linarith only [h1023, h1049, hlam]
                                          · linarith only [h1046, h775, hlam]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [hlam, p1038_0]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        rcases p1038_3 (m.d 0 5) (by simp) with h1054 | h1054
                                        · linarith only [h1054, h775, hlam]
                                        · linarith only [h1054, h807, hlam]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [h1023, h1026, h1029, h1031, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1038_1, u3ehi0]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        rcases p1038_3 (m.d 0 5) (by simp) with h1058 | h1058
                                        · linarith only [h1058, h775, hlam]
                                        · linarith only [h1025, h1058, hlam]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [h807, hlam, p1038_1]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [h1028, hlam, p1038_1]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [hlam, p1038_0]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [h1034, hlam, p1038_1]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [h807, hlam, hphi, ht0b, ht5b, p1038_1, u0elo1, u5ehi4]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [h1023, hc35, hlam, hphi, p1038_1, u3ehi0]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [h1030, hlam, p1038_1]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [h1026, h1030, hc12, hlam, hphi, ht01, ht0b, ht5b, p1038_1, u5ehi2]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [hlam, p1038_0]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [h1026, h1029, h1037, hc12, hlam, hphi, ht01, ht0b, ht5b, p1038_1, u5ehi4]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [h1025, hlam, p1038_0]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [h1031, hlam, p1038_0]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [h1036, hlam, p1038_0]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [h1037, hlam, p1038_0]
                                      · have p1038_0 := h1038c.1
                                        have p1038_1 := h1038c.2.1
                                        have p1038_2 := h1038c.2.2.1
                                        have p1038_3 := h1038c.2.2.2
                                        linarith only [hlam, p1038_0]
                                    · linarith only [h1036, h1037, h808, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                                  · linarith only [h1025, h1032, h1036, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                            · linarith only [h1025, h1031, h658, hlam]
                          · linarith only [h1029, h1030, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1080 | h1080
                          · linarith only [h1029, h1080, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1082 | h1082
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1083 | h1083
                              · linarith only [h1029, h1083, h512, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1085 | h1085
                                · linarith only [h1026, h1029, h1085, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1087 | h1087
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1088 | h1088
                                    · rcases h5bigk with h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [hlam, p1089_0]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h775, hlam, p1089_1]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h1085, hlam, hphi, ht0b, ht34, ht45, ht5b, p1089_1, u0elo4, u3ehi2]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h1023, hlam, p1089_0]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h1025, hlam, hphi, ht0b, ht5b, p1089_1, u0elo3, u5ehi4]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h1029, h1082, h1085, h807, hc34, hlam, hphi, p1089_1, u3ehi2]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [hlam, p1089_0]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h1029, h1082, h1085, hc34, hlam, hphi, p1089_1, u3ehi2]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h1080, hlam, p1089_0]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        rcases p1089_3 (m.d 0 5) (by simp) with h1099 | h1099
                                        · linarith only [h1099, h775, hlam]
                                        · linarith only [h1025, h1099, hlam]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h807, hlam, p1089_1]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h1028, hlam, p1089_1]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [hlam, p1089_0]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h1085, hlam, p1089_1]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h807, hlam, hphi, ht0b, ht5b, p1089_1, u0elo4, u5ehi4]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h1023, h1088, hc34, hlam, hphi, p1089_1, u3ehi0]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h1088, h775, hc01, hc34, hlam, hphi, ht12, ht23, p1089_1]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h1085, h1088, hc34, hlam, hphi, p1089_1, u3ehi2]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [hlam, p1089_0]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        rcases p1089_3 (m.d 0 5) (by simp) with h1111 | h1111
                                        · linarith only [h1023, h1111, hlam]
                                        · linarith only [h1025, h1111, hlam]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h1025, hlam, p1089_0]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h1082, hlam, p1089_0]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h1087, hlam, p1089_0]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [h1088, hlam, p1089_0]
                                      · have p1089_0 := h1089c.1
                                        have p1089_1 := h1089c.2.1
                                        have p1089_2 := h1089c.2.2.1
                                        have p1089_3 := h1089c.2.2.2
                                        linarith only [hlam, p1089_0]
                                    · linarith only [h1025, h1088, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                                  · linarith only [h1025, h1083, h1087, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                            · linarith only [h1025, h1082, h658, hlam]
                      · linarith only [h0, h1028, h807, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1123 | h1123
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1124 | h1124
                        · linarith only [h1025, h1026, h1027, h1124, h808, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1126 | h1126
                          · linarith only [h1124, h1126, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1128 | h1128
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1129 | h1129
                              · linarith only [h1124, h1129, h512, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h1026, h1027, h1129, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h0, h1025, h1027, h1128, h658, h807, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h1123, h807, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1134 | h1134
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1135 | h1135
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1136 | h1136
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1137 | h1137
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1138 | h1138
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1139 | h1139
                              · linarith only [h1026, h1134, h1139, h808, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                              · linarith only [h1026, h1134, h1136, h1139, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h1025, h1136, h1138, h808, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi0]
                          · linarith only [h1026, h1134, h1136, h1137, h808, hc35, hlam, hphi, u3ehi0]
                        · linarith only [h1026, h1134, h1136, hlam]
                      · linarith only [h0, h1135, h807, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1146 | h1146
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1147 | h1147
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1148 | h1148
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1149 | h1149
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1150 | h1150
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1151 | h1151
                                · linarith only [h1023, h1151, h807, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                                · linarith only [h0, h1134, h1150, h1151, h807, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                              · linarith only [h1023, h1026, h1146, h1147, h1148, h1150, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h1023, h1025, h1134, h1146, h1148, h1149, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi0]
                          · linarith only [h1147, h1148, h808, hc35, hlam, hphi, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1157 | h1157
                          · linarith only [h1147, h1157, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h1026, h1146, h1157, hlam]
                      · linarith only [h0, h1146, h807, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1161 | h1161
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1162 | h1162
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1163 | h1163
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1164 | h1164
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1165 | h1165
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1166 | h1166
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1167 | h1167
                              · linarith only [h1161, h1167, h808, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1169 | h1169
                                · linarith only [h1167, h1169, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1171 | h1171
                                  · linarith only [h1025, h1161, h1164, h1167, h1171, h808, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1173 | h1173
                                    · linarith only [h1025, h1161, h1164, h1173, h808, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                                    · linarith only [h1166, h1173, h808, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h1164, h1166, h808, hc45, hlam, hphi, ht34, u3ehi0]
                          · linarith only [h1164, h1165, h808, hc35, hlam, hphi, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1178 | h1178
                          · linarith only [h1164, h1178, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1180 | h1180
                            · linarith only [h1025, h1164, h1180, h808, hc34, hlam, hphi, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1182 | h1182
                              · linarith only [h1161, h1182, h808, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1184 | h1184
                                · linarith only [h1161, h1178, h1184, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1186 | h1186
                                  · linarith only [h1164, h1180, h1186, h512, hc01, hc24, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1188 | h1188
                                    · linarith only [h1164, h1180, h1188, h512, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · linarith only [h1188, h808, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h0, h1163, h807, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1192 | h1192
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1193 | h1193
                        · linarith only [h1161, h1162, h1193, h808, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1195 | h1195
                          · linarith only [h1193, h1195, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1197 | h1197
                            · linarith only [h1025, h1193, h1197, h808, hc34, hlam, hphi, u3ehi0]
                            · linarith only [h1161, h1162, h1197, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h1161, h1192, h807, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1201 | h1201
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1202 | h1202
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1203 | h1203
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1204 | h1204
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1205 | h1205
                            · linarith only [h1025, h1161, h1201, h1205, h808, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h1203, h1205, h808, hc45, hlam, hphi, ht34, u3ehi0]
                          · linarith only [h1203, h1204, h808, hc35, hlam, hphi, u3ehi0]
                        · linarith only [h1161, h1201, h1203, hlam]
                      · linarith only [h0, h1202, h807, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1211 | h1211
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1212 | h1212
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1213 | h1213
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1214 | h1214
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1215 | h1215
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1216 | h1216
                                · linarith only [h1023, h1216, h807, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                                · linarith only [h0, h1201, h1215, h1216, h807, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                              · linarith only [h1025, h1161, h1211, h1214, h1215, h808, hc34, hlam, hphi, u3ehi0]
                            · linarith only [h1023, h1201, h1211, h1213, h1214, hc45, hlam, hphi, ht34, u3ehi0]
                          · linarith only [h1212, h1213, h808, hc35, hlam, hphi, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1222 | h1222
                          · linarith only [h1212, h1222, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h1161, h1211, h1222, hlam]
                      · linarith only [h0, h1211, h807, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1226 | h1226
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1227 | h1227
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1228 | h1228
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1229 | h1229
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1230 | h1230
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1231 | h1231
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1232 | h1232
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1233 | h1233
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1234 | h1234
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1235 | h1235
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1236 | h1236
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1237 | h1237
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1238 | h1238
                                    · linarith only [h1226, h1238, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                    · linarith only [h1226, h1228, h1238, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                                  · linarith only [h1226, h1228, h1235, h1237, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                                · linarith only [h1227, h1236, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                              · linarith only [h1226, h1235, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                            · linarith only [h1228, h1234, h658, hlam]
                          · linarith only [h1227, h1233, h512, hlam]
                        · linarith only [h1226, h1232, h512, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1247 | h1247
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1248 | h1248
                          · linarith only [h1229, h1231, h1248, hlam]
                          · linarith only [h1227, h1248, h512, hlam]
                        · linarith only [h1226, h1247, h512, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1252 | h1252
                      · linarith only [h0, h1230, h1252, h807, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1254 | h1254
                        · linarith only [h1229, h1230, h1254, hlam]
                        · linarith only [h1226, h1254, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1257 | h1257
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1258 | h1258
                      · linarith only [h0, h1229, h1258, h807, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1260 | h1260
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1261 | h1261
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1262 | h1262
                            · linarith only [h1257, h1258, h1262, hlam]
                            · linarith only [h1228, h1262, h658, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h1226, h1227, h1261, h512, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4, u3ehi3]
                        · linarith only [h1226, h1260, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1267 | h1267
                      · linarith only [h0, h1229, h1267, h807, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1269 | h1269
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1270 | h1270
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1271 | h1271
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1272 | h1272
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1273 | h1273
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1274 | h1274
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1275 | h1275
                                    · linarith only [h1226, h1275, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                    · linarith only [h1226, h1228, h1275, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                                  · linarith only [h1228, h1257, h1274, h658, hlam]
                                · linarith only [h1227, h1273, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                              · linarith only [h1227, h1229, h1272, h512, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h1228, h1271, h658, hlam]
                          · linarith only [h1227, h1270, h512, hlam]
                        · linarith only [h1226, h1269, h512, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1284 | h1284
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1285 | h1285
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1286 | h1286
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1287 | h1287
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1288 | h1288
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1289 | h1289
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1290 | h1290
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1291 | h1291
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1292 | h1292
                                  · linarith only [h1228, h1284, h1290, h1292, h658, hc01, hc12, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1294 | h1294
                                    · linarith only [h1226, h1292, h1294, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                    · rcases h5bigk with h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [hlam, p1296_0]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h775, hlam, p1296_1]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h807, hlam, p1296_0]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h1294, hlam, hphi, ht0b, ht34, ht45, ht5b, p1296_1, u0elo4, u3ehi3]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h1228, hlam, p1296_1]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        rcases p1296_3 (m.d 0 5) (by simp) with h1302 | h1302
                                        · linarith only [h1302, h775, hlam]
                                        · rcases p1296_3 (m.d 1 5) (by simp) with h1304 | h1304
                                          · rcases p1296_3 (m.d 2 5) (by simp) with h1305 | h1305
                                            · linarith only [h1286, h1305, hlam]
                                            · linarith only [h1305, h807, hlam]
                                          · linarith only [h1304, h775, hlam]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [hlam, p1296_0]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h0, h1284, h1287, h1289, h807, hc01, hc12, hlam, hphi, p1296_1]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        rcases p1296_3 (m.d 0 5) (by simp) with h1311 | h1311
                                        · linarith only [h1311, h775, hlam]
                                        · linarith only [h1227, h1311, hlam]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h1226, h1228, h1284, h1287, h1289, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1296_1, u3ehi3]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h1286, hc12, hlam, hphi, ht01, ht0b, ht5b, p1296_1, u5ehi0]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h1286, hlam, p1296_1]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [hlam, p1296_0]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h1284, h1291, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1296_1, u3ehi4]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h1292, hlam, p1296_1]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h1227, hlam, p1296_1]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h1288, hlam, p1296_1]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h1291, hlam, p1296_0]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [hlam, p1296_0]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h1294, hlam, p1296_1]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h1226, h1228, hc45, hlam, hphi, ht34, p1296_1, u3ehi3]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h1289, hlam, p1296_0]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h1284, h1287, h1289, hc12, hlam, hphi, ht01, ht0b, ht5b, p1296_1, u5ehi2]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [h1284, h1287, h1289, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1296_1, u3ehi4]
                                      · have p1296_0 := h1296c.1
                                        have p1296_1 := h1296c.2.1
                                        have p1296_2 := h1296c.2.2.1
                                        have p1296_3 := h1296c.2.2.2
                                        linarith only [hlam, p1296_0]
                                · linarith only [h1227, h1291, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                              · linarith only [h1226, h1290, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1332 | h1332
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1333 | h1333
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1334 | h1334
                                  · linarith only [h1289, h1334, h658, hc01, hc24, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1336 | h1336
                                    · linarith only [h1226, h1289, h1336, h658, hlam]
                                    · rcases h5bigk with h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [hlam, p1338_0]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h775, hlam, p1338_1]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h807, hlam, p1338_0]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [hlam, hphi, ht0b, ht5b, p1338_1, u0elo4, u5ehi3]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h1228, hlam, p1338_1]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h1227, h1289, h1336, hc45, hlam, hphi, ht34, p1338_1, u3ehi3]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [hlam, p1338_0]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h0, h1289, h807, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1338_1]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h1289, h1336, hc45, hlam, hphi, ht34, p1338_1, u3ehi3]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h1289, hlam, p1338_1]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h1227, h1286, h1336, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1338_1, u3ehi3]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h1286, hlam, p1338_1]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [hlam, p1338_0]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h1284, h1333, h1336, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1338_1, u3ehi3]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h1334, hlam, p1338_1]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h1227, hlam, p1338_1]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h1288, hlam, p1338_1]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h1333, hlam, p1338_0]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [hlam, p1338_0]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h1336, hlam, p1338_1]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h1227, h1336, hc45, hlam, hphi, ht34, p1338_1, u3ehi3]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h775, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1338_1]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h0, h807, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1338_1]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [h1336, hc45, hlam, hphi, ht34, p1338_1, u3ehi3]
                                      · have p1338_0 := h1338c.1
                                        have p1338_1 := h1338c.2.1
                                        have p1338_2 := h1338c.2.2.1
                                        have p1338_3 := h1338c.2.2.2
                                        linarith only [hlam, p1338_0]
                                · linarith only [h1227, h1333, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                              · linarith only [h1226, h1332, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                          · linarith only [h1227, h1288, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                        · linarith only [h1226, h1287, h512, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1368 | h1368
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1369 | h1369
                          · linarith only [h1284, h1286, h1369, hlam]
                          · linarith only [h1227, h1369, h512, hlam]
                        · linarith only [h1226, h1368, h512, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1373 | h1373
                      · linarith only [h0, h1285, h1373, h807, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1375 | h1375
                        · linarith only [h1284, h1285, h1375, hlam]
                        · linarith only [h1226, h1375, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1378 | h1378
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1379 | h1379
                      · linarith only [h0, h1284, h1379, h807, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1381 | h1381
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1382 | h1382
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1383 | h1383
                            · linarith only [h1228, h1284, h1378, h1383, h658, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1385 | h1385
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1386 | h1386
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1387 | h1387
                                  · linarith only [h1378, h1379, h1383, h1386, h1387, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h1378, h1379, h1385, h1387, hc45, hlam, hphi, ht34, u3ehi3]
                                · linarith only [h1227, h1386, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                              · linarith only [h1226, h1284, h1378, h1379, h1385, h512, h658, hc01, hc25, hlam, hphi, ht12]
                          · linarith only [h1227, h1382, h512, hlam]
                        · linarith only [h1226, h1381, h512, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1394 | h1394
                      · linarith only [h0, h1284, h1394, h807, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1396 | h1396
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1397 | h1397
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1398 | h1398
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1399 | h1399
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1400 | h1400
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1401 | h1401
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1402 | h1402
                                    · linarith only [h1226, h1228, h1402, hlam]
                                    · rcases h5bigk with h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [hlam, p1404_0]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [h775, hlam, p1404_1]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [h807, hlam, p1404_0]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [h1402, hlam, hphi, ht0b, ht34, ht45, ht5b, p1404_1, u0elo4, u3ehi3]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [h1228, hlam, p1404_1]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        rcases p1404_3 (m.d 0 5) (by simp) with h1410 | h1410
                                        · linarith only [h1410, h775, hlam]
                                        · rcases p1404_3 (m.d 1 5) (by simp) with h1412 | h1412
                                          · rcases p1404_3 (m.d 2 5) (by simp) with h1413 | h1413
                                            · rcases p1404_3 (m.d 3 5) (by simp) with h1414 | h1414
                                              · linarith only [h1397, h1414, hlam]
                                              · rcases p1404_3 (m.d 4 5) (by simp) with h1416 | h1416
                                                · linarith only [h1398, h1416, hlam]
                                                · linarith only [h1228, h1416, hlam]
                                            · linarith only [h1413, h807, hlam]
                                          · linarith only [h1412, h775, hlam]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [hlam, p1404_0]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [h1394, hlam, p1404_0]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        rcases p1404_3 (m.d 0 5) (by simp) with h1423 | h1423
                                        · linarith only [h1423, h775, hlam]
                                        · linarith only [h1227, h1423, hlam]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [h1226, h1228, h1284, h1396, h1398, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1404_1, u3ehi3]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        rcases p1404_3 (m.d 0 5) (by simp) with h1427 | h1427
                                        · linarith only [h1427, h807, hlam]
                                        · rcases p1404_3 (m.d 1 5) (by simp) with h1429 | h1429
                                          · linarith only [h1394, h1429, hlam]
                                          · linarith only [h1429, h775, hlam]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [h1399, h1401, h775, hc01, hc23, hlam, hphi, ht12, p1404_1]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [hlam, p1404_0]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        rcases p1404_3 (m.d 0 5) (by simp) with h1434 | h1434
                                        · linarith only [h1434, h807, hlam]
                                        · linarith only [h1227, h1434, hlam]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [h1226, h1228, h1399, h1401, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1404_1, u3ehi3]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [h1227, hlam, p1404_1]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [h1397, hlam, p1404_1]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [h1400, hlam, p1404_0]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [hlam, p1404_0]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [h1402, hlam, p1404_1]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [h1227, h1402, hc45, hlam, hphi, ht34, p1404_1, u3ehi3]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [h1398, hlam, p1404_0]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [h1401, hlam, p1404_0]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [h1284, h1396, h1398, h1402, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1404_1, u3ehi3]
                                      · have p1404_0 := h1404c.1
                                        have p1404_1 := h1404c.2.1
                                        have p1404_2 := h1404c.2.2.1
                                        have p1404_3 := h1404c.2.2.2
                                        linarith only [hlam, p1404_0]
                                  · linarith only [h0, h1284, h1378, h1396, h1398, h1401, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h1227, h1284, h1400, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                              · linarith only [h1226, h1228, h1284, h1396, h1398, h1399, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1451 | h1451
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1452 | h1452
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1453 | h1453
                                  · linarith only [h0, h1378, h1398, h1453, hc01, hc24, hlam, hphi, ht12]
                                  · linarith only [h0, h1378, h1453, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · linarith only [h1227, h1284, h1452, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                              · linarith only [h1226, h1227, h1284, h1451, h512, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                          · linarith only [h1227, h1397, h512, hlam]
                        · linarith only [h1226, h1396, h512, hlam]
              · linarith only [h1226, h1227, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1461 | h1461
              · linarith only [h1226, h1461, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1463 | h1463
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1464 | h1464
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1465 | h1465
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1466 | h1466
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1467 | h1467
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1468 | h1468
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1469 | h1469
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1470 | h1470
                              · linarith only [h1226, h1464, h1470, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1472 | h1472
                                · linarith only [h1461, h1467, h1470, h1472, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1474 | h1474
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1475 | h1475
                                    · rcases h5bigk with h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [hlam, p1476_0]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [h775, hlam, p1476_1]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [h807, hlam, p1476_0]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [h1461, hlam, p1476_0]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [hlam, hphi, ht0b, ht5b, p1476_1, u0elo4, u5ehi4]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        rcases p1476_3 (m.d 0 5) (by simp) with h1482 | h1482
                                        · linarith only [h1482, h775, hlam]
                                        · rcases p1476_3 (m.d 1 5) (by simp) with h1484 | h1484
                                          · rcases p1476_3 (m.d 2 5) (by simp) with h1485 | h1485
                                            · linarith only [h1466, h1485, hlam]
                                            · linarith only [h1485, h807, hlam]
                                          · linarith only [h1484, h775, hlam]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [hlam, p1476_0]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [h0, h1464, h1467, h1469, h807, hc01, hc12, hlam, hphi, p1476_1]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [h1461, h1464, h1467, h1469, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1476_1, u3ehi0]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        rcases p1476_3 (m.d 0 5) (by simp) with h1492 | h1492
                                        · linarith only [h1492, h775, hlam]
                                        · linarith only [h1463, h1492, hlam]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [h1466, hc12, hlam, hphi, ht01, ht0b, ht5b, p1476_1, u5ehi0]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [h1466, hlam, p1476_1]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [hlam, p1476_0]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [h1472, hlam, p1476_1]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [h1465, h1474, hc12, hlam, hphi, ht01, ht0b, ht5b, p1476_1, u5ehi4]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [h1461, hc35, hlam, hphi, p1476_1, u3ehi0]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [h1468, hlam, p1476_1]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [h1464, h1468, hc12, hlam, hphi, ht01, ht0b, ht5b, p1476_1, u5ehi2]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [hlam, p1476_0]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [h1464, h1467, h1475, hc12, hlam, hphi, ht01, ht0b, ht5b, p1476_1, u5ehi4]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [h1463, hlam, p1476_0]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [h1469, hlam, p1476_0]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [h1474, hlam, p1476_0]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [h1475, hlam, p1476_0]
                                      · have p1476_0 := h1476c.1
                                        have p1476_1 := h1476c.2.1
                                        have p1476_2 := h1476c.2.2.1
                                        have p1476_3 := h1476c.2.2.2
                                        linarith only [hlam, p1476_0]
                                    · linarith only [h1226, h1475, hc45, hlam, hphi, ht34, u3ehi0]
                                  · linarith only [h1463, h1470, h1474, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                            · linarith only [h1463, h1469, h658, hlam]
                          · linarith only [h1467, h1468, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1514 | h1514
                          · linarith only [h1467, h1514, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1516 | h1516
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1517 | h1517
                              · linarith only [h1467, h1517, h512, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1519 | h1519
                                · linarith only [h1464, h1514, h1519, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1521 | h1521
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1522 | h1522
                                    · rcases h5bigk with h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h775, hlam, p1523_1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h807, hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1461, hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [hlam, hphi, ht0b, ht5b, p1523_1, u0elo4, u5ehi4]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1461, h1467, h1516, hc34, hlam, hphi, p1523_1, u3ehi0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h0, h1467, h1516, h807, hc01, hc34, hlam, hphi, ht12, ht23, p1523_1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1514, hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        rcases p1523_3 (m.d 0 5) (by simp) with h1533 | h1533
                                        · linarith only [h1533, h775, hlam]
                                        · linarith only [h1463, h1533, hlam]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1461, h1466, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1523_1, u3ehi0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1466, hlam, p1523_1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1519, hlam, p1523_1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1465, h1521, hc12, hlam, hphi, ht01, ht0b, ht5b, p1523_1, u5ehi4]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1461, hc35, hlam, hphi, p1523_1, u3ehi0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h775, hc01, hc35, hlam, hphi, ht12, ht23, p1523_1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h0, h807, hc01, hc35, hlam, hphi, ht12, ht23, p1523_1]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        rcases p1523_3 (m.d 0 5) (by simp) with h1545 | h1545
                                        · linarith only [h1461, h1545, hlam]
                                        · linarith only [h1463, h1545, hlam]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1463, hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1516, hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1521, hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [h1522, hlam, p1523_0]
                                      · have p1523_0 := h1523c.1
                                        have p1523_1 := h1523c.2.1
                                        have p1523_2 := h1523c.2.2.1
                                        have p1523_3 := h1523c.2.2.2
                                        linarith only [hlam, p1523_0]
                                    · linarith only [h1463, h1522, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                                  · linarith only [h1463, h1517, h1521, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                            · linarith only [h1463, h1516, h658, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1556 | h1556
                        · linarith only [h1226, h1464, h1466, h1556, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1558 | h1558
                          · linarith only [h1556, h1558, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1560 | h1560
                            · linarith only [h1465, h1466, h1560, hlam]
                            · linarith only [h1463, h1560, h658, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1563 | h1563
                      · linarith only [h0, h1465, h1563, h807, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1565 | h1565
                        · linarith only [h1226, h1464, h1563, h1565, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1567 | h1567
                          · linarith only [h1565, h1567, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1569 | h1569
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1570 | h1570
                              · linarith only [h1565, h1570, h512, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h1464, h1465, h1570, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h1463, h1569, h658, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1574 | h1574
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1575 | h1575
                      · linarith only [h1464, h1575, h807, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1577 | h1577
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1578 | h1578
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1579 | h1579
                            · linarith only [h1574, h1575, h1579, hlam]
                            · linarith only [h1226, h1463, h1577, h1579, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi0]
                          · linarith only [h1226, h1577, h1578, hc35, hlam, hphi, u3ehi0]
                        · linarith only [h1464, h1574, h1577, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1584 | h1584
                      · linarith only [h0, h1574, h1584, h807, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1586 | h1586
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1587 | h1587
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1588 | h1588
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1589 | h1589
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1590 | h1590
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1591 | h1591
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1592 | h1592
                                    · rcases h5bigk with h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [hlam, p1593_0]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [h775, hlam, p1593_1]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [h807, hlam, p1593_0]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [h1461, hlam, p1593_0]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [h1463, hlam, hphi, ht0b, ht5b, p1593_1, u0elo3, u5ehi4]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        rcases p1593_3 (m.d 0 5) (by simp) with h1599 | h1599
                                        · linarith only [h1599, h775, hlam]
                                        · rcases p1593_3 (m.d 1 5) (by simp) with h1601 | h1601
                                          · rcases p1593_3 (m.d 2 5) (by simp) with h1602 | h1602
                                            · rcases p1593_3 (m.d 3 5) (by simp) with h1603 | h1603
                                              · linarith only [h1587, h1603, hlam]
                                              · linarith only [h1461, h1603, hlam]
                                            · linarith only [h1602, h807, hlam]
                                          · linarith only [h1601, h775, hlam]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [hlam, p1593_0]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [h1584, hlam, p1593_0]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [h1461, h1584, h1589, h1591, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1593_1, u3ehi0]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        rcases p1593_3 (m.d 0 5) (by simp) with h1611 | h1611
                                        · linarith only [h1611, h775, hlam]
                                        · linarith only [h1463, h1611, hlam]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        rcases p1593_3 (m.d 0 5) (by simp) with h1614 | h1614
                                        · linarith only [h1614, h807, hlam]
                                        · rcases p1593_3 (m.d 1 5) (by simp) with h1616 | h1616
                                          · linarith only [h1584, h1616, hlam]
                                          · linarith only [h1616, h775, hlam]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [h1589, h1591, h775, hc01, hc23, hlam, hphi, ht12, p1593_1]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [hlam, p1593_0]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [h1461, h1589, h1591, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1593_1, u3ehi0]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        rcases p1593_3 (m.d 0 5) (by simp) with h1622 | h1622
                                        · linarith only [h1622, h807, hlam]
                                        · linarith only [h1463, h1622, hlam]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [h1461, h1586, h1592, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1593_1, u3ehi0]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [h1587, hlam, p1593_1]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [h1590, hlam, p1593_0]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [hlam, p1593_0]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [h1464, h1586, h1592, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1593_1, u5ehi4]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [h1463, hlam, p1593_0]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [h1588, hlam, p1593_0]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [h1591, hlam, p1593_0]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [h1592, hlam, p1593_0]
                                      · have p1593_0 := h1593c.1
                                        have p1593_1 := h1593c.2.1
                                        have p1593_2 := h1593c.2.2.1
                                        have p1593_3 := h1593c.2.2.2
                                        linarith only [hlam, p1593_0]
                                    · linarith only [h1463, h1592, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                                  · linarith only [h0, h1226, h1464, h1574, h1586, h1591, hc01, hc23, hc45, hlam, hphi, ht12, ht34, u3ehi0]
                                · linarith only [h1226, h1464, h1586, h1587, h1588, h1590, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · linarith only [h1464, h1587, h1589, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h1226, h1463, h1464, h1586, h1588, h658, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h1226, h1463, h1586, h1587, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1641 | h1641
                          · linarith only [h1586, h1641, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1643 | h1643
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1644 | h1644
                              · linarith only [h1586, h1644, h512, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h1464, h1644, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1463, h1643, h658, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1648 | h1648
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1649 | h1649
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1650 | h1650
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1651 | h1651
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1652 | h1652
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1653 | h1653
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1654 | h1654
                              · linarith only [h1226, h1648, h1654, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1656 | h1656
                                · linarith only [h1654, h1656, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1658 | h1658
                                  · linarith only [h1226, h1463, h1648, h1651, h1654, h1658, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1660 | h1660
                                    · linarith only [h1226, h1463, h1648, h1651, h1660, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                                    · linarith only [h1226, h1660, hc45, hlam, hphi, ht34, u3ehi0]
                            · linarith only [h1226, h1651, h1653, hc45, hlam, hphi, ht34, u3ehi0]
                          · linarith only [h1226, h1651, h1652, hc35, hlam, hphi, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1665 | h1665
                          · linarith only [h1651, h1665, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1667 | h1667
                            · linarith only [h1226, h1463, h1651, h1667, hc34, hlam, hphi, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1669 | h1669
                              · linarith only [h1226, h1648, h1669, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1671 | h1671
                                · linarith only [h1648, h1651, h1667, h1671, hc45, hlam, hphi, ht34, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1673 | h1673
                                  · linarith only [h1649, h1667, h1673, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1675 | h1675
                                    · linarith only [h1651, h1667, h1675, hc34, hlam, hphi, u3ehi1]
                                    · linarith only [h1226, h1675, hc45, hlam, hphi, ht34, u3ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1678 | h1678
                        · linarith only [h1226, h1648, h1650, h1678, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1680 | h1680
                          · linarith only [h1678, h1680, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1682 | h1682
                            · linarith only [h1226, h1463, h1649, h1650, h1682, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1684 | h1684
                              · linarith only [h1648, h1650, h1684, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1686 | h1686
                                · linarith only [h1649, h1650, h1680, h1684, h1686, h512, hc01, hc25, hlam, hphi, ht12]
                                · linarith only [h1649, h1650, h1684, h1686, hc35, hlam, hphi, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1689 | h1689
                      · linarith only [h0, h1649, h1689, h807, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1691 | h1691
                        · linarith only [h1226, h1648, h1649, h1691, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1693 | h1693
                          · linarith only [h1691, h1693, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1695 | h1695
                            · linarith only [h1226, h1463, h1691, h1695, hc34, hlam, hphi, u3ehi0]
                            · linarith only [h1648, h1649, h1695, hc45, hlam, hphi, ht34, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1698 | h1698
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1699 | h1699
                      · linarith only [h0, h1648, h1699, h807, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1701 | h1701
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1702 | h1702
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1703 | h1703
                            · linarith only [h1226, h1463, h1648, h1698, h1703, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h1226, h1701, h1703, hc45, hlam, hphi, ht34, u3ehi0]
                          · linarith only [h1226, h1701, h1702, hc35, hlam, hphi, u3ehi0]
                        · linarith only [h1648, h1698, h1701, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1708 | h1708
                      · linarith only [h0, h1698, h1708, h807, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1710 | h1710
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1711 | h1711
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1712 | h1712
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1713 | h1713
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1714 | h1714
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1715 | h1715
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1716 | h1716
                                    · linarith only [h1226, h1463, h1716, hc34, hlam, hphi, u3ehi0]
                                    · linarith only [h1226, h1710, h1712, h1716, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                                  · linarith only [h0, h1648, h1698, h1710, h1712, h1715, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h1648, h1711, h1714, hlam]
                              · linarith only [h1648, h1711, h1713, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h1226, h1710, h1712, hc45, hlam, hphi, ht34, u3ehi0]
                          · linarith only [h1226, h1710, h1711, hc35, hlam, hphi, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1724 | h1724
                          · linarith only [h1710, h1724, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1726 | h1726
                            · linarith only [h1226, h1463, h1710, h1726, hc34, hlam, hphi, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1728 | h1728
                              · linarith only [h1710, h1728, h512, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h1648, h1728, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 3432000 in
theorem n7l_sBT3_M_LR_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h3bigk := hb3.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases h3bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 3) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 3) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 3 5) (by simp) with h7 | h7
            · rcases h5bigk with h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hlam, p8_0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p8_1, u0elo4, u5ehi1]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p8_1, u0elo4, u5ehi2]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p8_1, u0elo4, u5ehi3]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p8_1, u0elo4, u5ehi4]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p8_1, u0ehi9]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hlam, p8_0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                rcases p8_3 (m.d 0 5) (by simp) with h16 | h16
                · linarith only [h16, hlam, hphi, ht0b, ht5b, p8_1, u0elo4, u5ehi2]
                · linarith only [h16, hc15, hlam, hphi, ht01, p8_1, u0ehi9]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h7, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p8_1]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                rcases p8_3 (m.d 0 5) (by simp) with h20 | h20
                · linarith only [h20, hlam, hphi, ht0b, ht5b, p8_1, u0elo4, u5ehi4]
                · linarith only [h20, hc15, hlam, hphi, ht01, p8_1, u0ehi9]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p8_1, u0ehi9]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                rcases p8_3 (m.d 0 5) (by simp) with h24 | h24
                · linarith only [h24, hlam, hphi, ht0b, ht5b, p8_1, u0elo4, u5ehi1]
                · linarith only [h24, hc25, hlam, hphi, ht01, ht12, p8_1, u0ehi9]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hlam, p8_0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p8_1]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                rcases p8_3 (m.d 0 5) (by simp) with h29 | h29
                · linarith only [h29, hlam, hphi, ht0b, ht5b, p8_1, u0elo4, u5ehi4]
                · linarith only [h29, hc25, hlam, hphi, ht01, ht12, p8_1, u0ehi9]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p8_1, u0ehi9]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                rcases p8_3 (m.d 0 5) (by simp) with h33 | h33
                · linarith only [h33, hlam, hphi, ht0b, ht5b, p8_1, u0elo4, u5ehi1]
                · linarith only [h33, hc35, hlam, hphi, ht01, ht12, ht23, p8_1, u0ehi9]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                rcases p8_3 (m.d 0 5) (by simp) with h36 | h36
                · linarith only [h36, hlam, hphi, ht0b, ht5b, p8_1, u0elo4, u5ehi2]
                · linarith only [h36, hc35, hlam, hphi, ht01, ht12, ht23, p8_1, u0ehi9]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hlam, p8_0]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                rcases p8_3 (m.d 0 5) (by simp) with h40 | h40
                · linarith only [h40, hlam, hphi, ht0b, ht5b, p8_1, u0elo4, u5ehi4]
                · linarith only [h40, hc35, hlam, hphi, ht01, ht12, ht23, p8_1, u0ehi9]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p8_1, u0ehi9]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                rcases p8_3 (m.d 0 5) (by simp) with h44 | h44
                · linarith only [h44, hlam, hphi, ht0b, ht5b, p8_1, u0elo4, u5ehi1]
                · linarith only [h44, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p8_1, u0ehi9]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                rcases p8_3 (m.d 0 5) (by simp) with h47 | h47
                · linarith only [h47, hlam, hphi, ht0b, ht5b, p8_1, u0elo4, u5ehi2]
                · linarith only [h47, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p8_1, u0ehi9]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [h7, hc13, hc45, hlam, hphi, ht34, p0_1, p8_1]
              · have p8_0 := h8c.1
                have p8_1 := h8c.2.1
                have p8_2 := h8c.2.2.1
                have p8_3 := h8c.2.2.2
                linarith only [hlam, p8_0]
            · linarith only [h7, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
          · rcases p0_3 (m.d 3 5) (by simp) with h53 | h53
            · rcases h5bigk with h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                linarith only [hlam, p54_0]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p54_1, u0elo4, u5ehi1]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p54_1, u0elo4, u5ehi2]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                linarith only [h53, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p54_1, u0elo4]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p54_1, u0elo4, u5ehi4]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p54_1, u0ehi9]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                linarith only [hlam, p54_0]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                rcases p54_3 (m.d 0 5) (by simp) with h62 | h62
                · linarith only [h62, hlam, hphi, ht0b, ht5b, p54_1, u0elo4, u5ehi2]
                · linarith only [h62, hc15, hlam, hphi, ht01, p54_1, u0ehi9]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                linarith only [h53, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p54_1]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                rcases p54_3 (m.d 0 5) (by simp) with h66 | h66
                · linarith only [h66, hlam, hphi, ht0b, ht5b, p54_1, u0elo4, u5ehi4]
                · linarith only [h66, hc15, hlam, hphi, ht01, p54_1, u0ehi9]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p54_1, u0ehi9]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                rcases p54_3 (m.d 0 5) (by simp) with h70 | h70
                · linarith only [h70, hlam, hphi, ht0b, ht5b, p54_1, u0elo4, u5ehi1]
                · linarith only [h70, hc25, hlam, hphi, ht01, ht12, p54_1, u0ehi9]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                linarith only [hlam, p54_0]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                linarith only [h53, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p54_1]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                rcases p54_3 (m.d 0 5) (by simp) with h75 | h75
                · linarith only [h75, hlam, hphi, ht0b, ht5b, p54_1, u0elo4, u5ehi4]
                · linarith only [h75, hc25, hlam, hphi, ht01, ht12, p54_1, u0ehi9]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p54_1, u0ehi9]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                rcases p54_3 (m.d 0 5) (by simp) with h79 | h79
                · linarith only [h79, hlam, hphi, ht0b, ht5b, p54_1, u0elo4, u5ehi1]
                · linarith only [h79, hc35, hlam, hphi, ht01, ht12, ht23, p54_1, u0ehi9]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                rcases p54_3 (m.d 0 5) (by simp) with h82 | h82
                · linarith only [h82, hlam, hphi, ht0b, ht5b, p54_1, u0elo4, u5ehi2]
                · linarith only [h82, hc35, hlam, hphi, ht01, ht12, ht23, p54_1, u0ehi9]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                linarith only [hlam, p54_0]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                rcases p54_3 (m.d 0 5) (by simp) with h86 | h86
                · linarith only [h86, hlam, hphi, ht0b, ht5b, p54_1, u0elo4, u5ehi4]
                · linarith only [h86, hc35, hlam, hphi, ht01, ht12, ht23, p54_1, u0ehi9]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p54_1, u0ehi9]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                rcases p54_3 (m.d 0 5) (by simp) with h90 | h90
                · linarith only [h90, hlam, hphi, ht0b, ht5b, p54_1, u0elo4, u5ehi1]
                · linarith only [h90, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p54_1, u0ehi9]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                rcases p54_3 (m.d 0 5) (by simp) with h93 | h93
                · linarith only [h93, hlam, hphi, ht0b, ht5b, p54_1, u0elo4, u5ehi2]
                · linarith only [h93, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p54_1, u0ehi9]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                linarith only [h53, hc13, hc45, hlam, hphi, ht34, p0_1, p54_1]
              · have p54_0 := h54c.1
                have p54_1 := h54c.2.1
                have p54_2 := h54c.2.2.1
                have p54_3 := h54c.2.2.2
                linarith only [hlam, p54_0]
            · linarith only [h53, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
        · rcases p0_3 (m.d 3 4) (by simp) with h99 | h99
          · rcases p0_3 (m.d 3 5) (by simp) with h100 | h100
            · rcases h5bigk with h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                linarith only [hlam, p101_0]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p101_1, u0elo4, u5ehi1]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p101_1, u0elo4, u5ehi2]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                linarith only [h100, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p101_1, u0elo4]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p101_1, u0elo4, u5ehi4]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p101_1, u0ehi9]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                linarith only [hlam, p101_0]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                rcases p101_3 (m.d 0 5) (by simp) with h109 | h109
                · linarith only [h109, hlam, hphi, ht0b, ht5b, p101_1, u0elo4, u5ehi2]
                · linarith only [h109, hc15, hlam, hphi, ht01, p101_1, u0ehi9]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                linarith only [h100, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p101_1]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                rcases p101_3 (m.d 0 5) (by simp) with h113 | h113
                · linarith only [h113, hlam, hphi, ht0b, ht5b, p101_1, u0elo4, u5ehi4]
                · linarith only [h113, hc15, hlam, hphi, ht01, p101_1, u0ehi9]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p101_1, u0ehi9]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                rcases p101_3 (m.d 0 5) (by simp) with h117 | h117
                · linarith only [h117, hlam, hphi, ht0b, ht5b, p101_1, u0elo4, u5ehi1]
                · linarith only [h117, hc25, hlam, hphi, ht01, ht12, p101_1, u0ehi9]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                linarith only [hlam, p101_0]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                linarith only [h100, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p101_1]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                rcases p101_3 (m.d 0 5) (by simp) with h122 | h122
                · linarith only [h122, hlam, hphi, ht0b, ht5b, p101_1, u0elo4, u5ehi4]
                · linarith only [h122, hc25, hlam, hphi, ht01, ht12, p101_1, u0ehi9]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p101_1, u0ehi9]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                rcases p101_3 (m.d 0 5) (by simp) with h126 | h126
                · linarith only [h126, hlam, hphi, ht0b, ht5b, p101_1, u0elo4, u5ehi1]
                · linarith only [h126, hc35, hlam, hphi, ht01, ht12, ht23, p101_1, u0ehi9]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                rcases p101_3 (m.d 0 5) (by simp) with h129 | h129
                · linarith only [h129, hlam, hphi, ht0b, ht5b, p101_1, u0elo4, u5ehi2]
                · linarith only [h129, hc35, hlam, hphi, ht01, ht12, ht23, p101_1, u0ehi9]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                linarith only [hlam, p101_0]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                rcases p101_3 (m.d 0 5) (by simp) with h133 | h133
                · linarith only [h133, hlam, hphi, ht0b, ht5b, p101_1, u0elo4, u5ehi4]
                · linarith only [h133, hc35, hlam, hphi, ht01, ht12, ht23, p101_1, u0ehi9]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p101_1, u0ehi9]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                rcases p101_3 (m.d 0 5) (by simp) with h137 | h137
                · linarith only [h137, hlam, hphi, ht0b, ht5b, p101_1, u0elo4, u5ehi1]
                · linarith only [h137, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p101_1, u0ehi9]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                rcases p101_3 (m.d 0 5) (by simp) with h140 | h140
                · linarith only [h140, hlam, hphi, ht0b, ht5b, p101_1, u0elo4, u5ehi2]
                · linarith only [h140, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p101_1, u0ehi9]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                linarith only [h100, hc13, hc45, hlam, hphi, ht34, p0_1, p101_1]
              · have p101_0 := h101c.1
                have p101_1 := h101c.2.1
                have p101_2 := h101c.2.2.1
                have p101_3 := h101c.2.2.2
                linarith only [hlam, p101_0]
            · linarith only [h100, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
          · rcases p0_3 (m.d 3 5) (by simp) with h146 | h146
            · rcases h5bigk with h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p147_1, u0elo4, u5ehi1]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p147_1, u0elo4, u5ehi2]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h146, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p147_1, u0elo4]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p147_1, u0elo4, u5ehi4]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p147_1, u0ehi9]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                rcases p147_3 (m.d 0 5) (by simp) with h155 | h155
                · linarith only [h155, hlam, hphi, ht0b, ht5b, p147_1, u0elo4, u5ehi2]
                · linarith only [h155, hc15, hlam, hphi, ht01, p147_1, u0ehi9]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h146, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p147_1]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                rcases p147_3 (m.d 0 5) (by simp) with h159 | h159
                · linarith only [h159, hlam, hphi, ht0b, ht5b, p147_1, u0elo4, u5ehi4]
                · linarith only [h159, hc15, hlam, hphi, ht01, p147_1, u0ehi9]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p147_1, u0ehi9]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                rcases p147_3 (m.d 0 5) (by simp) with h163 | h163
                · linarith only [h163, hlam, hphi, ht0b, ht5b, p147_1, u0elo4, u5ehi1]
                · linarith only [h163, hc25, hlam, hphi, ht01, ht12, p147_1, u0ehi9]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h146, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p147_1]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                rcases p147_3 (m.d 0 5) (by simp) with h168 | h168
                · linarith only [h168, hlam, hphi, ht0b, ht5b, p147_1, u0elo4, u5ehi4]
                · linarith only [h168, hc25, hlam, hphi, ht01, ht12, p147_1, u0ehi9]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p147_1, u0ehi9]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                rcases p147_3 (m.d 0 5) (by simp) with h172 | h172
                · linarith only [h172, hlam, hphi, ht0b, ht5b, p147_1, u0elo4, u5ehi1]
                · linarith only [h172, hc35, hlam, hphi, ht01, ht12, ht23, p147_1, u0ehi9]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                rcases p147_3 (m.d 0 5) (by simp) with h175 | h175
                · linarith only [h175, hlam, hphi, ht0b, ht5b, p147_1, u0elo4, u5ehi2]
                · linarith only [h175, hc35, hlam, hphi, ht01, ht12, ht23, p147_1, u0ehi9]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                rcases p147_3 (m.d 0 5) (by simp) with h179 | h179
                · linarith only [h179, hlam, hphi, ht0b, ht5b, p147_1, u0elo4, u5ehi4]
                · linarith only [h179, hc35, hlam, hphi, ht01, ht12, ht23, p147_1, u0ehi9]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p147_1, u0ehi9]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                rcases p147_3 (m.d 0 5) (by simp) with h183 | h183
                · linarith only [h183, hlam, hphi, ht0b, ht5b, p147_1, u0elo4, u5ehi1]
                · linarith only [h183, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p147_1, u0ehi9]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                rcases p147_3 (m.d 0 5) (by simp) with h186 | h186
                · linarith only [h186, hlam, hphi, ht0b, ht5b, p147_1, u0elo4, u5ehi2]
                · linarith only [h186, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p147_1, u0ehi9]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h146, hc13, hc45, hlam, hphi, ht34, p0_1, p147_1]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, p147_0]
            · linarith only [h146, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 3) (by simp) with h193 | h193
    · rcases p0_3 (m.d 1 3) (by simp) with h194 | h194
      · rcases p0_3 (m.d 2 3) (by simp) with h195 | h195
        · linarith only [h195, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h197 | h197
          · rcases p0_3 (m.d 3 5) (by simp) with h198 | h198
            · rcases h5bigk with h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                linarith only [hlam, p199_0]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p199_1, u0elo4, u5ehi1]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p199_1, u0elo4, u5ehi2]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                linarith only [h198, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p199_1, u0elo4]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p199_1, u0elo4, u5ehi4]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p199_1, u0ehi9]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                linarith only [hlam, p199_0]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                rcases p199_3 (m.d 0 5) (by simp) with h207 | h207
                · linarith only [h207, hlam, hphi, ht0b, ht5b, p199_1, u0elo4, u5ehi2]
                · linarith only [h207, hc15, hlam, hphi, ht01, p199_1, u0ehi9]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                linarith only [h198, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p199_1]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                rcases p199_3 (m.d 0 5) (by simp) with h211 | h211
                · linarith only [h211, hlam, hphi, ht0b, ht5b, p199_1, u0elo4, u5ehi4]
                · linarith only [h211, hc15, hlam, hphi, ht01, p199_1, u0ehi9]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p199_1, u0ehi9]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                rcases p199_3 (m.d 0 5) (by simp) with h215 | h215
                · linarith only [h215, hlam, hphi, ht0b, ht5b, p199_1, u0elo4, u5ehi1]
                · linarith only [h215, hc25, hlam, hphi, ht01, ht12, p199_1, u0ehi9]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                linarith only [hlam, p199_0]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                linarith only [h198, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p199_1]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                rcases p199_3 (m.d 0 5) (by simp) with h220 | h220
                · linarith only [h220, hlam, hphi, ht0b, ht5b, p199_1, u0elo4, u5ehi4]
                · linarith only [h220, hc25, hlam, hphi, ht01, ht12, p199_1, u0ehi9]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p199_1, u0ehi9]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                rcases p199_3 (m.d 0 5) (by simp) with h224 | h224
                · linarith only [h224, hlam, hphi, ht0b, ht5b, p199_1, u0elo4, u5ehi1]
                · linarith only [h224, hc35, hlam, hphi, ht01, ht12, ht23, p199_1, u0ehi9]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                rcases p199_3 (m.d 0 5) (by simp) with h227 | h227
                · linarith only [h227, hlam, hphi, ht0b, ht5b, p199_1, u0elo4, u5ehi2]
                · linarith only [h227, hc35, hlam, hphi, ht01, ht12, ht23, p199_1, u0ehi9]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                linarith only [hlam, p199_0]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                rcases p199_3 (m.d 0 5) (by simp) with h231 | h231
                · linarith only [h231, hlam, hphi, ht0b, ht5b, p199_1, u0elo4, u5ehi4]
                · linarith only [h231, hc35, hlam, hphi, ht01, ht12, ht23, p199_1, u0ehi9]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p199_1, u0ehi9]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                rcases p199_3 (m.d 0 5) (by simp) with h235 | h235
                · linarith only [h235, hlam, hphi, ht0b, ht5b, p199_1, u0elo4, u5ehi1]
                · linarith only [h235, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p199_1, u0ehi9]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                rcases p199_3 (m.d 0 5) (by simp) with h238 | h238
                · linarith only [h238, hlam, hphi, ht0b, ht5b, p199_1, u0elo4, u5ehi2]
                · linarith only [h238, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p199_1, u0ehi9]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                linarith only [h198, hc23, hc45, hlam, hphi, ht34, p0_1, p199_1]
              · have p199_0 := h199c.1
                have p199_1 := h199c.2.1
                have p199_2 := h199c.2.2.1
                have p199_3 := h199c.2.2.2
                linarith only [hlam, p199_0]
            · linarith only [h198, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
          · rcases p0_3 (m.d 3 5) (by simp) with h244 | h244
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
                linarith only [hlam, hphi, ht0b, ht5b, p245_1, u0elo4, u5ehi1]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p245_1, u0elo4, u5ehi2]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                linarith only [h244, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p245_1, u0elo4]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p245_1, u0elo4, u5ehi4]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p245_1, u0ehi9]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                linarith only [hlam, p245_0]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                rcases p245_3 (m.d 0 5) (by simp) with h253 | h253
                · linarith only [h253, hlam, hphi, ht0b, ht5b, p245_1, u0elo4, u5ehi2]
                · linarith only [h253, hc15, hlam, hphi, ht01, p245_1, u0ehi9]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                linarith only [h244, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p245_1]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                rcases p245_3 (m.d 0 5) (by simp) with h257 | h257
                · linarith only [h257, hlam, hphi, ht0b, ht5b, p245_1, u0elo4, u5ehi4]
                · linarith only [h257, hc15, hlam, hphi, ht01, p245_1, u0ehi9]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p245_1, u0ehi9]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                rcases p245_3 (m.d 0 5) (by simp) with h261 | h261
                · linarith only [h261, hlam, hphi, ht0b, ht5b, p245_1, u0elo4, u5ehi1]
                · linarith only [h261, hc25, hlam, hphi, ht01, ht12, p245_1, u0ehi9]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                linarith only [hlam, p245_0]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                linarith only [h244, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p245_1]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                rcases p245_3 (m.d 0 5) (by simp) with h266 | h266
                · linarith only [h266, hlam, hphi, ht0b, ht5b, p245_1, u0elo4, u5ehi4]
                · linarith only [h266, hc25, hlam, hphi, ht01, ht12, p245_1, u0ehi9]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p245_1, u0ehi9]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                rcases p245_3 (m.d 0 5) (by simp) with h270 | h270
                · linarith only [h270, hlam, hphi, ht0b, ht5b, p245_1, u0elo4, u5ehi1]
                · linarith only [h270, hc35, hlam, hphi, ht01, ht12, ht23, p245_1, u0ehi9]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                rcases p245_3 (m.d 0 5) (by simp) with h273 | h273
                · linarith only [h273, hlam, hphi, ht0b, ht5b, p245_1, u0elo4, u5ehi2]
                · linarith only [h273, hc35, hlam, hphi, ht01, ht12, ht23, p245_1, u0ehi9]
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
                · linarith only [h277, hlam, hphi, ht0b, ht5b, p245_1, u0elo4, u5ehi4]
                · linarith only [h277, hc35, hlam, hphi, ht01, ht12, ht23, p245_1, u0ehi9]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p245_1, u0ehi9]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                rcases p245_3 (m.d 0 5) (by simp) with h281 | h281
                · linarith only [h281, hlam, hphi, ht0b, ht5b, p245_1, u0elo4, u5ehi1]
                · linarith only [h281, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p245_1, u0ehi9]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                rcases p245_3 (m.d 0 5) (by simp) with h284 | h284
                · linarith only [h284, hlam, hphi, ht0b, ht5b, p245_1, u0elo4, u5ehi2]
                · linarith only [h284, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p245_1, u0ehi9]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                linarith only [h244, hc23, hc45, hlam, hphi, ht34, p0_1, p245_1]
              · have p245_0 := h245c.1
                have p245_1 := h245c.2.1
                have p245_2 := h245c.2.2.1
                have p245_3 := h245c.2.2.2
                linarith only [hlam, p245_0]
            · linarith only [h244, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
      · rcases p0_3 (m.d 2 3) (by simp) with h290 | h290
        · linarith only [h290, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h292 | h292
          · rcases p0_3 (m.d 3 5) (by simp) with h293 | h293
            · rcases h5bigk with h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [hlam, p294_0]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p294_1, u0elo4, u5ehi1]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p294_1, u0elo4, u5ehi2]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h194, h293, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p294_1, u0elo4]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p294_1, u0elo4, u5ehi4]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p294_1, u0ehi9]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [hlam, p294_0]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                rcases p294_3 (m.d 0 5) (by simp) with h302 | h302
                · linarith only [h302, hlam, hphi, ht0b, ht5b, p294_1, u0elo4, u5ehi2]
                · linarith only [h302, hc15, hlam, hphi, ht01, p294_1, u0ehi9]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h194, h293, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p294_1]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                rcases p294_3 (m.d 0 5) (by simp) with h306 | h306
                · linarith only [h306, hlam, hphi, ht0b, ht5b, p294_1, u0elo4, u5ehi4]
                · linarith only [h306, hc15, hlam, hphi, ht01, p294_1, u0ehi9]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p294_1, u0ehi9]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                rcases p294_3 (m.d 0 5) (by simp) with h310 | h310
                · linarith only [h310, hlam, hphi, ht0b, ht5b, p294_1, u0elo4, u5ehi1]
                · linarith only [h310, hc25, hlam, hphi, ht01, ht12, p294_1, u0ehi9]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [hlam, p294_0]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h194, h293, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p294_1]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                rcases p294_3 (m.d 0 5) (by simp) with h315 | h315
                · linarith only [h315, hlam, hphi, ht0b, ht5b, p294_1, u0elo4, u5ehi4]
                · linarith only [h315, hc25, hlam, hphi, ht01, ht12, p294_1, u0ehi9]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p294_1, u0ehi9]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                rcases p294_3 (m.d 0 5) (by simp) with h319 | h319
                · linarith only [h319, hlam, hphi, ht0b, ht5b, p294_1, u0elo4, u5ehi1]
                · linarith only [h319, hc35, hlam, hphi, ht01, ht12, ht23, p294_1, u0ehi9]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                rcases p294_3 (m.d 0 5) (by simp) with h322 | h322
                · linarith only [h322, hlam, hphi, ht0b, ht5b, p294_1, u0elo4, u5ehi2]
                · linarith only [h322, hc35, hlam, hphi, ht01, ht12, ht23, p294_1, u0ehi9]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [hlam, p294_0]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                rcases p294_3 (m.d 0 5) (by simp) with h326 | h326
                · linarith only [h326, hlam, hphi, ht0b, ht5b, p294_1, u0elo4, u5ehi4]
                · linarith only [h326, hc35, hlam, hphi, ht01, ht12, ht23, p294_1, u0ehi9]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p294_1, u0ehi9]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                rcases p294_3 (m.d 0 5) (by simp) with h330 | h330
                · linarith only [h330, hlam, hphi, ht0b, ht5b, p294_1, u0elo4, u5ehi1]
                · linarith only [h330, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p294_1, u0ehi9]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                rcases p294_3 (m.d 0 5) (by simp) with h333 | h333
                · linarith only [h333, hlam, hphi, ht0b, ht5b, p294_1, u0elo4, u5ehi2]
                · linarith only [h333, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p294_1, u0ehi9]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h194, h293, hc13, hc45, hlam, hphi, ht34, p0_1, p294_1]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [hlam, p294_0]
            · linarith only [h293, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
          · rcases p0_3 (m.d 3 5) (by simp) with h339 | h339
            · rcases h5bigk with h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hlam, p340_0]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p340_1, u0elo4, u5ehi1]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p340_1, u0elo4, u5ehi2]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [h339, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p340_1, u0elo4]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p340_1, u0elo4, u5ehi4]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p340_1, u0ehi9]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hlam, p340_0]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                rcases p340_3 (m.d 0 5) (by simp) with h348 | h348
                · linarith only [h348, hlam, hphi, ht0b, ht5b, p340_1, u0elo4, u5ehi2]
                · linarith only [h348, hc15, hlam, hphi, ht01, p340_1, u0ehi9]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [h339, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p340_1]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                rcases p340_3 (m.d 0 5) (by simp) with h352 | h352
                · linarith only [h352, hlam, hphi, ht0b, ht5b, p340_1, u0elo4, u5ehi4]
                · linarith only [h352, hc15, hlam, hphi, ht01, p340_1, u0ehi9]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p340_1, u0ehi9]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                rcases p340_3 (m.d 0 5) (by simp) with h356 | h356
                · linarith only [h356, hlam, hphi, ht0b, ht5b, p340_1, u0elo4, u5ehi1]
                · linarith only [h356, hc25, hlam, hphi, ht01, ht12, p340_1, u0ehi9]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hlam, p340_0]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [h339, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p340_1]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                rcases p340_3 (m.d 0 5) (by simp) with h361 | h361
                · linarith only [h361, hlam, hphi, ht0b, ht5b, p340_1, u0elo4, u5ehi4]
                · linarith only [h361, hc25, hlam, hphi, ht01, ht12, p340_1, u0ehi9]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p340_1, u0ehi9]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                rcases p340_3 (m.d 0 5) (by simp) with h365 | h365
                · linarith only [h365, hlam, hphi, ht0b, ht5b, p340_1, u0elo4, u5ehi1]
                · linarith only [h365, hc35, hlam, hphi, ht01, ht12, ht23, p340_1, u0ehi9]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                rcases p340_3 (m.d 0 5) (by simp) with h368 | h368
                · linarith only [h368, hlam, hphi, ht0b, ht5b, p340_1, u0elo4, u5ehi2]
                · linarith only [h368, hc35, hlam, hphi, ht01, ht12, ht23, p340_1, u0ehi9]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hlam, p340_0]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                rcases p340_3 (m.d 0 5) (by simp) with h372 | h372
                · linarith only [h372, hlam, hphi, ht0b, ht5b, p340_1, u0elo4, u5ehi4]
                · linarith only [h372, hc35, hlam, hphi, ht01, ht12, ht23, p340_1, u0ehi9]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p340_1, u0ehi9]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                rcases p340_3 (m.d 0 5) (by simp) with h376 | h376
                · linarith only [h376, hlam, hphi, ht0b, ht5b, p340_1, u0elo4, u5ehi1]
                · linarith only [h376, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p340_1, u0ehi9]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                rcases p340_3 (m.d 0 5) (by simp) with h379 | h379
                · linarith only [h379, hlam, hphi, ht0b, ht5b, p340_1, u0elo4, u5ehi2]
                · linarith only [h379, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p340_1, u0ehi9]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [h339, hc23, hc45, hlam, hphi, ht34, p0_1, p340_1]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hlam, p340_0]
            · linarith only [h339, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
    · linarith only [h193, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 3) (by simp) with h386 | h386
    · rcases p0_3 (m.d 1 3) (by simp) with h387 | h387
      · rcases p0_3 (m.d 2 3) (by simp) with h388 | h388
        · rcases p0_3 (m.d 3 4) (by simp) with h389 | h389
          · linarith only [h389, hlam, p0_0]
          · rcases p0_3 (m.d 3 5) (by simp) with h391 | h391
            · rcases h5bigk with h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                linarith only [hlam, p392_0]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p392_1, u0elo4, u5ehi1]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p392_1, u0elo4, u5ehi2]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                linarith only [h391, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p392_1, u0elo4]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p392_1, u0elo4, u5ehi4]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p392_1, u0ehi9]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                linarith only [hlam, p392_0]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                rcases p392_3 (m.d 0 5) (by simp) with h400 | h400
                · linarith only [h400, hlam, hphi, ht0b, ht5b, p392_1, u0elo4, u5ehi2]
                · linarith only [h400, hc15, hlam, hphi, ht01, p392_1, u0ehi9]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                linarith only [h391, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, p392_1]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                rcases p392_3 (m.d 0 5) (by simp) with h404 | h404
                · linarith only [h404, hlam, hphi, ht0b, ht5b, p392_1, u0elo4, u5ehi4]
                · linarith only [h404, hc15, hlam, hphi, ht01, p392_1, u0ehi9]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p392_1, u0ehi9]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                rcases p392_3 (m.d 0 5) (by simp) with h408 | h408
                · linarith only [h408, hlam, hphi, ht0b, ht5b, p392_1, u0elo4, u5ehi1]
                · linarith only [h408, hc25, hlam, hphi, ht01, ht12, p392_1, u0ehi9]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                linarith only [hlam, p392_0]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                linarith only [h391, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, p392_1]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                rcases p392_3 (m.d 0 5) (by simp) with h413 | h413
                · linarith only [h413, hlam, hphi, ht0b, ht5b, p392_1, u0elo4, u5ehi4]
                · linarith only [h413, hc25, hlam, hphi, ht01, ht12, p392_1, u0ehi9]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p392_1, u0ehi9]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                rcases p392_3 (m.d 0 5) (by simp) with h417 | h417
                · linarith only [h417, hlam, hphi, ht0b, ht5b, p392_1, u0elo4, u5ehi1]
                · linarith only [h417, hc35, hlam, hphi, ht01, ht12, ht23, p392_1, u0ehi9]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                rcases p392_3 (m.d 0 5) (by simp) with h420 | h420
                · linarith only [h420, hlam, hphi, ht0b, ht5b, p392_1, u0elo4, u5ehi2]
                · linarith only [h420, hc35, hlam, hphi, ht01, ht12, ht23, p392_1, u0ehi9]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                linarith only [hlam, p392_0]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                rcases p392_3 (m.d 0 5) (by simp) with h424 | h424
                · linarith only [h424, hlam, hphi, ht0b, ht5b, p392_1, u0elo4, u5ehi4]
                · linarith only [h424, hc35, hlam, hphi, ht01, ht12, ht23, p392_1, u0ehi9]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p392_1, u0ehi9]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                rcases p392_3 (m.d 0 5) (by simp) with h428 | h428
                · linarith only [h428, hlam, hphi, ht0b, ht5b, p392_1, u0elo4, u5ehi1]
                · linarith only [h428, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p392_1, u0ehi9]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                rcases p392_3 (m.d 0 5) (by simp) with h431 | h431
                · linarith only [h431, hlam, hphi, ht0b, ht5b, p392_1, u0elo4, u5ehi2]
                · linarith only [h431, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p392_1, u0ehi9]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                linarith only [h391, hc34, hc45, hlam, hphi, p0_1, p392_1]
              · have p392_0 := h392c.1
                have p392_1 := h392c.2.1
                have p392_2 := h392c.2.2.1
                have p392_3 := h392c.2.2.2
                linarith only [hlam, p392_0]
            · linarith only [h391, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
        · rcases p0_3 (m.d 3 4) (by simp) with h437 | h437
          · linarith only [h437, hlam, p0_0]
          · rcases p0_3 (m.d 3 5) (by simp) with h439 | h439
            · rcases h5bigk with h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                linarith only [hlam, p440_0]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p440_1, u0elo4, u5ehi1]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p440_1, u0elo4, u5ehi2]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                linarith only [h388, h439, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p440_1, u0elo4]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p440_1, u0elo4, u5ehi4]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p440_1, u0ehi9]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                linarith only [hlam, p440_0]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                rcases p440_3 (m.d 0 5) (by simp) with h448 | h448
                · linarith only [h448, hlam, hphi, ht0b, ht5b, p440_1, u0elo4, u5ehi2]
                · linarith only [h448, hc15, hlam, hphi, ht01, p440_1, u0ehi9]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                linarith only [h388, h439, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p440_1]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                rcases p440_3 (m.d 0 5) (by simp) with h452 | h452
                · linarith only [h452, hlam, hphi, ht0b, ht5b, p440_1, u0elo4, u5ehi4]
                · linarith only [h452, hc15, hlam, hphi, ht01, p440_1, u0ehi9]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p440_1, u0ehi9]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                rcases p440_3 (m.d 0 5) (by simp) with h456 | h456
                · linarith only [h456, hlam, hphi, ht0b, ht5b, p440_1, u0elo4, u5ehi1]
                · linarith only [h456, hc25, hlam, hphi, ht01, ht12, p440_1, u0ehi9]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                linarith only [hlam, p440_0]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                linarith only [h388, h439, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p440_1]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                rcases p440_3 (m.d 0 5) (by simp) with h461 | h461
                · linarith only [h461, hlam, hphi, ht0b, ht5b, p440_1, u0elo4, u5ehi4]
                · linarith only [h461, hc25, hlam, hphi, ht01, ht12, p440_1, u0ehi9]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p440_1, u0ehi9]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                rcases p440_3 (m.d 0 5) (by simp) with h465 | h465
                · linarith only [h465, hlam, hphi, ht0b, ht5b, p440_1, u0elo4, u5ehi1]
                · linarith only [h465, hc35, hlam, hphi, ht01, ht12, ht23, p440_1, u0ehi9]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                rcases p440_3 (m.d 0 5) (by simp) with h468 | h468
                · linarith only [h468, hlam, hphi, ht0b, ht5b, p440_1, u0elo4, u5ehi2]
                · linarith only [h468, hc35, hlam, hphi, ht01, ht12, ht23, p440_1, u0ehi9]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                linarith only [hlam, p440_0]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                rcases p440_3 (m.d 0 5) (by simp) with h472 | h472
                · linarith only [h472, hlam, hphi, ht0b, ht5b, p440_1, u0elo4, u5ehi4]
                · linarith only [h472, hc35, hlam, hphi, ht01, ht12, ht23, p440_1, u0ehi9]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p440_1, u0ehi9]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                rcases p440_3 (m.d 0 5) (by simp) with h476 | h476
                · linarith only [h476, hlam, hphi, ht0b, ht5b, p440_1, u0elo4, u5ehi1]
                · linarith only [h476, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p440_1, u0ehi9]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                rcases p440_3 (m.d 0 5) (by simp) with h479 | h479
                · linarith only [h479, hlam, hphi, ht0b, ht5b, p440_1, u0elo4, u5ehi2]
                · linarith only [h479, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p440_1, u0ehi9]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                linarith only [h388, h439, hc23, hc45, hlam, hphi, ht34, p0_1, p440_1]
              · have p440_0 := h440c.1
                have p440_1 := h440c.2.1
                have p440_2 := h440c.2.2.1
                have p440_3 := h440c.2.2.2
                linarith only [hlam, p440_0]
            · linarith only [h439, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
      · rcases p0_3 (m.d 2 3) (by simp) with h485 | h485
        · rcases p0_3 (m.d 3 4) (by simp) with h486 | h486
          · linarith only [h486, hlam, p0_0]
          · rcases p0_3 (m.d 3 5) (by simp) with h488 | h488
            · rcases h5bigk with h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                linarith only [hlam, p489_0]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p489_1, u0elo4, u5ehi1]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p489_1, u0elo4, u5ehi2]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                linarith only [h387, h488, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p489_1, u0elo4]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p489_1, u0elo4, u5ehi4]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p489_1, u0ehi9]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                linarith only [hlam, p489_0]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                rcases p489_3 (m.d 0 5) (by simp) with h497 | h497
                · linarith only [h497, hlam, hphi, ht0b, ht5b, p489_1, u0elo4, u5ehi2]
                · linarith only [h497, hc15, hlam, hphi, ht01, p489_1, u0ehi9]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                linarith only [h387, h488, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p489_1]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                rcases p489_3 (m.d 0 5) (by simp) with h501 | h501
                · linarith only [h501, hlam, hphi, ht0b, ht5b, p489_1, u0elo4, u5ehi4]
                · linarith only [h501, hc15, hlam, hphi, ht01, p489_1, u0ehi9]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p489_1, u0ehi9]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                rcases p489_3 (m.d 0 5) (by simp) with h505 | h505
                · linarith only [h505, hlam, hphi, ht0b, ht5b, p489_1, u0elo4, u5ehi1]
                · linarith only [h505, hc25, hlam, hphi, ht01, ht12, p489_1, u0ehi9]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                linarith only [hlam, p489_0]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                linarith only [h387, h488, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p489_1]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                rcases p489_3 (m.d 0 5) (by simp) with h510 | h510
                · linarith only [h510, hlam, hphi, ht0b, ht5b, p489_1, u0elo4, u5ehi4]
                · linarith only [h510, hc25, hlam, hphi, ht01, ht12, p489_1, u0ehi9]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p489_1, u0ehi9]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                rcases p489_3 (m.d 0 5) (by simp) with h514 | h514
                · linarith only [h514, hlam, hphi, ht0b, ht5b, p489_1, u0elo4, u5ehi1]
                · linarith only [h514, hc35, hlam, hphi, ht01, ht12, ht23, p489_1, u0ehi9]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                rcases p489_3 (m.d 0 5) (by simp) with h517 | h517
                · linarith only [h517, hlam, hphi, ht0b, ht5b, p489_1, u0elo4, u5ehi2]
                · linarith only [h517, hc35, hlam, hphi, ht01, ht12, ht23, p489_1, u0ehi9]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                linarith only [hlam, p489_0]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                rcases p489_3 (m.d 0 5) (by simp) with h521 | h521
                · linarith only [h521, hlam, hphi, ht0b, ht5b, p489_1, u0elo4, u5ehi4]
                · linarith only [h521, hc35, hlam, hphi, ht01, ht12, ht23, p489_1, u0ehi9]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p489_1, u0ehi9]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                rcases p489_3 (m.d 0 5) (by simp) with h525 | h525
                · linarith only [h525, hlam, hphi, ht0b, ht5b, p489_1, u0elo4, u5ehi1]
                · linarith only [h525, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p489_1, u0ehi9]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                rcases p489_3 (m.d 0 5) (by simp) with h528 | h528
                · linarith only [h528, hlam, hphi, ht0b, ht5b, p489_1, u0elo4, u5ehi2]
                · linarith only [h528, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p489_1, u0ehi9]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                linarith only [h387, h488, hc13, hc45, hlam, hphi, ht34, p0_1, p489_1]
              · have p489_0 := h489c.1
                have p489_1 := h489c.2.1
                have p489_2 := h489c.2.2.1
                have p489_3 := h489c.2.2.2
                linarith only [hlam, p489_0]
            · linarith only [h488, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
        · rcases p0_3 (m.d 3 4) (by simp) with h534 | h534
          · linarith only [h534, hlam, p0_0]
          · rcases p0_3 (m.d 3 5) (by simp) with h536 | h536
            · rcases h5bigk with h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                linarith only [hlam, p537_0]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p537_1, u0elo4, u5ehi1]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p537_1, u0elo4, u5ehi2]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                linarith only [h485, h536, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p537_1, u0elo4]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p537_1, u0elo4, u5ehi4]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p537_1, u0ehi9]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                linarith only [hlam, p537_0]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                rcases p537_3 (m.d 0 5) (by simp) with h545 | h545
                · linarith only [h545, hlam, hphi, ht0b, ht5b, p537_1, u0elo4, u5ehi2]
                · linarith only [h545, hc15, hlam, hphi, ht01, p537_1, u0ehi9]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                linarith only [h485, h536, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p537_1]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                rcases p537_3 (m.d 0 5) (by simp) with h549 | h549
                · linarith only [h549, hlam, hphi, ht0b, ht5b, p537_1, u0elo4, u5ehi4]
                · linarith only [h549, hc15, hlam, hphi, ht01, p537_1, u0ehi9]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p537_1, u0ehi9]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                rcases p537_3 (m.d 0 5) (by simp) with h553 | h553
                · linarith only [h553, hlam, hphi, ht0b, ht5b, p537_1, u0elo4, u5ehi1]
                · linarith only [h553, hc25, hlam, hphi, ht01, ht12, p537_1, u0ehi9]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                linarith only [hlam, p537_0]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                linarith only [h485, h536, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p537_1]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                rcases p537_3 (m.d 0 5) (by simp) with h558 | h558
                · linarith only [h558, hlam, hphi, ht0b, ht5b, p537_1, u0elo4, u5ehi4]
                · linarith only [h558, hc25, hlam, hphi, ht01, ht12, p537_1, u0ehi9]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p537_1, u0ehi9]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                rcases p537_3 (m.d 0 5) (by simp) with h562 | h562
                · linarith only [h562, hlam, hphi, ht0b, ht5b, p537_1, u0elo4, u5ehi1]
                · linarith only [h562, hc35, hlam, hphi, ht01, ht12, ht23, p537_1, u0ehi9]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                rcases p537_3 (m.d 0 5) (by simp) with h565 | h565
                · linarith only [h565, hlam, hphi, ht0b, ht5b, p537_1, u0elo4, u5ehi2]
                · linarith only [h565, hc35, hlam, hphi, ht01, ht12, ht23, p537_1, u0ehi9]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                linarith only [hlam, p537_0]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                rcases p537_3 (m.d 0 5) (by simp) with h569 | h569
                · linarith only [h569, hlam, hphi, ht0b, ht5b, p537_1, u0elo4, u5ehi4]
                · linarith only [h569, hc35, hlam, hphi, ht01, ht12, ht23, p537_1, u0ehi9]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p537_1, u0ehi9]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                rcases p537_3 (m.d 0 5) (by simp) with h573 | h573
                · linarith only [h573, hlam, hphi, ht0b, ht5b, p537_1, u0elo4, u5ehi1]
                · linarith only [h573, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p537_1, u0ehi9]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                rcases p537_3 (m.d 0 5) (by simp) with h576 | h576
                · linarith only [h576, hlam, hphi, ht0b, ht5b, p537_1, u0elo4, u5ehi2]
                · linarith only [h576, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p537_1, u0ehi9]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                linarith only [h485, h536, hc23, hc45, hlam, hphi, ht34, p0_1, p537_1]
              · have p537_0 := h537c.1
                have p537_1 := h537c.2.1
                have p537_2 := h537c.2.2.1
                have p537_3 := h537c.2.2.2
                linarith only [hlam, p537_0]
            · linarith only [h536, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
    · linarith only [h386, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi7]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 3) (by simp) with h586 | h586
    · rcases p0_3 (m.d 1 3) (by simp) with h587 | h587
      · rcases p0_3 (m.d 2 3) (by simp) with h588 | h588
        · linarith only [h588, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h590 | h590
          · rcases p0_3 (m.d 3 5) (by simp) with h591 | h591
            · rcases h5bigk with h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p592_1, u0elo4, u5ehi1]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p592_1, u0elo4, u5ehi2]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p592_1, u0elo4, u5ehi3]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p592_1, u0elo4, u5ehi4]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p592_1, u0ehi9]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                rcases p592_3 (m.d 0 5) (by simp) with h600 | h600
                · linarith only [h600, hlam, hphi, ht0b, ht5b, p592_1, u0elo4, u5ehi2]
                · linarith only [h600, hc15, hlam, hphi, ht01, p592_1, u0ehi9]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h591, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p592_1]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                rcases p592_3 (m.d 0 5) (by simp) with h604 | h604
                · linarith only [h604, hlam, hphi, ht0b, ht5b, p592_1, u0elo4, u5ehi4]
                · linarith only [h604, hc15, hlam, hphi, ht01, p592_1, u0ehi9]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p592_1, u0ehi9]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                rcases p592_3 (m.d 0 5) (by simp) with h608 | h608
                · linarith only [h608, hlam, hphi, ht0b, ht5b, p592_1, u0elo4, u5ehi1]
                · linarith only [h608, hc25, hlam, hphi, ht01, ht12, p592_1, u0ehi9]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h591, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p592_1]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                rcases p592_3 (m.d 0 5) (by simp) with h613 | h613
                · linarith only [h613, hlam, hphi, ht0b, ht5b, p592_1, u0elo4, u5ehi4]
                · linarith only [h613, hc25, hlam, hphi, ht01, ht12, p592_1, u0ehi9]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p592_1, u0ehi9]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                rcases p592_3 (m.d 0 5) (by simp) with h617 | h617
                · linarith only [h617, hlam, hphi, ht0b, ht5b, p592_1, u0elo4, u5ehi1]
                · linarith only [h617, hc35, hlam, hphi, ht01, ht12, ht23, p592_1, u0ehi9]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                rcases p592_3 (m.d 0 5) (by simp) with h620 | h620
                · linarith only [h620, hlam, hphi, ht0b, ht5b, p592_1, u0elo4, u5ehi2]
                · linarith only [h620, hc35, hlam, hphi, ht01, ht12, ht23, p592_1, u0ehi9]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                rcases p592_3 (m.d 0 5) (by simp) with h624 | h624
                · linarith only [h624, hlam, hphi, ht0b, ht5b, p592_1, u0elo4, u5ehi4]
                · linarith only [h624, hc35, hlam, hphi, ht01, ht12, ht23, p592_1, u0ehi9]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p592_1, u0ehi9]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                rcases p592_3 (m.d 0 5) (by simp) with h628 | h628
                · linarith only [h628, hlam, hphi, ht0b, ht5b, p592_1, u0elo4, u5ehi1]
                · linarith only [h628, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p592_1, u0ehi9]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                rcases p592_3 (m.d 0 5) (by simp) with h631 | h631
                · linarith only [h631, hlam, hphi, ht0b, ht5b, p592_1, u0elo4, u5ehi2]
                · linarith only [h631, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p592_1, u0ehi9]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h591, hc23, hc45, hlam, hphi, ht34, p0_1, p592_1]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hlam, p592_0]
            · linarith only [h586, h591, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
          · rcases p0_3 (m.d 3 5) (by simp) with h637 | h637
            · rcases h5bigk with h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                linarith only [hlam, p638_0]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p638_1, u0elo4, u5ehi1]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p638_1, u0elo4, u5ehi2]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                linarith only [h637, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p638_1, u0elo4]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p638_1, u0elo4, u5ehi4]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p638_1, u0ehi9]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                linarith only [hlam, p638_0]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                rcases p638_3 (m.d 0 5) (by simp) with h646 | h646
                · linarith only [h646, hlam, hphi, ht0b, ht5b, p638_1, u0elo4, u5ehi2]
                · linarith only [h646, hc15, hlam, hphi, ht01, p638_1, u0ehi9]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                linarith only [h637, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p638_1]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                rcases p638_3 (m.d 0 5) (by simp) with h650 | h650
                · linarith only [h650, hlam, hphi, ht0b, ht5b, p638_1, u0elo4, u5ehi4]
                · linarith only [h650, hc15, hlam, hphi, ht01, p638_1, u0ehi9]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p638_1, u0ehi9]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                rcases p638_3 (m.d 0 5) (by simp) with h654 | h654
                · linarith only [h654, hlam, hphi, ht0b, ht5b, p638_1, u0elo4, u5ehi1]
                · linarith only [h654, hc25, hlam, hphi, ht01, ht12, p638_1, u0ehi9]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                linarith only [hlam, p638_0]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                linarith only [h637, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p638_1]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                rcases p638_3 (m.d 0 5) (by simp) with h659 | h659
                · linarith only [h659, hlam, hphi, ht0b, ht5b, p638_1, u0elo4, u5ehi4]
                · linarith only [h659, hc25, hlam, hphi, ht01, ht12, p638_1, u0ehi9]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p638_1, u0ehi9]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                rcases p638_3 (m.d 0 5) (by simp) with h663 | h663
                · linarith only [h663, hlam, hphi, ht0b, ht5b, p638_1, u0elo4, u5ehi1]
                · linarith only [h663, hc35, hlam, hphi, ht01, ht12, ht23, p638_1, u0ehi9]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                rcases p638_3 (m.d 0 5) (by simp) with h666 | h666
                · linarith only [h666, hlam, hphi, ht0b, ht5b, p638_1, u0elo4, u5ehi2]
                · linarith only [h666, hc35, hlam, hphi, ht01, ht12, ht23, p638_1, u0ehi9]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                linarith only [hlam, p638_0]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                rcases p638_3 (m.d 0 5) (by simp) with h670 | h670
                · linarith only [h670, hlam, hphi, ht0b, ht5b, p638_1, u0elo4, u5ehi4]
                · linarith only [h670, hc35, hlam, hphi, ht01, ht12, ht23, p638_1, u0ehi9]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p638_1, u0ehi9]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                rcases p638_3 (m.d 0 5) (by simp) with h674 | h674
                · linarith only [h674, hlam, hphi, ht0b, ht5b, p638_1, u0elo4, u5ehi1]
                · linarith only [h674, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p638_1, u0ehi9]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                rcases p638_3 (m.d 0 5) (by simp) with h677 | h677
                · linarith only [h677, hlam, hphi, ht0b, ht5b, p638_1, u0elo4, u5ehi2]
                · linarith only [h677, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p638_1, u0ehi9]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                linarith only [h637, hc23, hc45, hlam, hphi, ht34, p0_1, p638_1]
              · have p638_0 := h638c.1
                have p638_1 := h638c.2.1
                have p638_2 := h638c.2.2.1
                have p638_3 := h638c.2.2.2
                linarith only [hlam, p638_0]
            · linarith only [h586, h637, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
      · linarith only [h587, hlam, p0_0]
    · linarith only [h586, hc13, hlam, hphi, ht01, p0_1, u0ehi7]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 3) (by simp) with h685 | h685
    · rcases p0_3 (m.d 1 3) (by simp) with h686 | h686
      · rcases p0_3 (m.d 2 3) (by simp) with h687 | h687
        · rcases p0_3 (m.d 3 4) (by simp) with h688 | h688
          · linarith only [h688, hlam, p0_0]
          · rcases p0_3 (m.d 3 5) (by simp) with h690 | h690
            · rcases h5bigk with h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                linarith only [hlam, p691_0]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p691_1, u0elo4, u5ehi1]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p691_1, u0elo4, u5ehi2]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                linarith only [h690, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p691_1, u0elo4]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p691_1, u0elo4, u5ehi4]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p691_1, u0ehi9]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                linarith only [hlam, p691_0]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                rcases p691_3 (m.d 0 5) (by simp) with h699 | h699
                · linarith only [h699, hlam, hphi, ht0b, ht5b, p691_1, u0elo4, u5ehi2]
                · linarith only [h699, hc15, hlam, hphi, ht01, p691_1, u0ehi9]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                linarith only [h690, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, p691_1]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                rcases p691_3 (m.d 0 5) (by simp) with h703 | h703
                · linarith only [h703, hlam, hphi, ht0b, ht5b, p691_1, u0elo4, u5ehi4]
                · linarith only [h703, hc15, hlam, hphi, ht01, p691_1, u0ehi9]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p691_1, u0ehi9]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                rcases p691_3 (m.d 0 5) (by simp) with h707 | h707
                · linarith only [h707, hlam, hphi, ht0b, ht5b, p691_1, u0elo4, u5ehi1]
                · linarith only [h707, hc25, hlam, hphi, ht01, ht12, p691_1, u0ehi9]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                linarith only [hlam, p691_0]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                linarith only [h690, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, p691_1]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                rcases p691_3 (m.d 0 5) (by simp) with h712 | h712
                · linarith only [h712, hlam, hphi, ht0b, ht5b, p691_1, u0elo4, u5ehi4]
                · linarith only [h712, hc25, hlam, hphi, ht01, ht12, p691_1, u0ehi9]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p691_1, u0ehi9]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                rcases p691_3 (m.d 0 5) (by simp) with h716 | h716
                · linarith only [h716, hlam, hphi, ht0b, ht5b, p691_1, u0elo4, u5ehi1]
                · linarith only [h716, hc35, hlam, hphi, ht01, ht12, ht23, p691_1, u0ehi9]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                rcases p691_3 (m.d 0 5) (by simp) with h719 | h719
                · linarith only [h719, hlam, hphi, ht0b, ht5b, p691_1, u0elo4, u5ehi2]
                · linarith only [h719, hc35, hlam, hphi, ht01, ht12, ht23, p691_1, u0ehi9]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                linarith only [hlam, p691_0]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                rcases p691_3 (m.d 0 5) (by simp) with h723 | h723
                · linarith only [h723, hlam, hphi, ht0b, ht5b, p691_1, u0elo4, u5ehi4]
                · linarith only [h723, hc35, hlam, hphi, ht01, ht12, ht23, p691_1, u0ehi9]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p691_1, u0ehi9]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                rcases p691_3 (m.d 0 5) (by simp) with h727 | h727
                · linarith only [h727, hlam, hphi, ht0b, ht5b, p691_1, u0elo4, u5ehi1]
                · linarith only [h727, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p691_1, u0ehi9]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                rcases p691_3 (m.d 0 5) (by simp) with h730 | h730
                · linarith only [h730, hlam, hphi, ht0b, ht5b, p691_1, u0elo4, u5ehi2]
                · linarith only [h730, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p691_1, u0ehi9]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                linarith only [h690, hc34, hc45, hlam, hphi, p0_1, p691_1]
              · have p691_0 := h691c.1
                have p691_1 := h691c.2.1
                have p691_2 := h691c.2.2.1
                have p691_3 := h691c.2.2.2
                linarith only [hlam, p691_0]
            · linarith only [h685, h690, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
        · rcases p0_3 (m.d 3 4) (by simp) with h736 | h736
          · linarith only [h736, hlam, p0_0]
          · rcases p0_3 (m.d 3 5) (by simp) with h738 | h738
            · rcases h5bigk with h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                linarith only [hlam, p739_0]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p739_1, u0elo4, u5ehi1]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p739_1, u0elo4, u5ehi2]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                linarith only [h687, h738, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p739_1, u0elo4]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p739_1, u0elo4, u5ehi4]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p739_1, u0ehi9]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                linarith only [hlam, p739_0]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                rcases p739_3 (m.d 0 5) (by simp) with h747 | h747
                · linarith only [h747, hlam, hphi, ht0b, ht5b, p739_1, u0elo4, u5ehi2]
                · linarith only [h747, hc15, hlam, hphi, ht01, p739_1, u0ehi9]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                linarith only [h687, h738, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p739_1]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                rcases p739_3 (m.d 0 5) (by simp) with h751 | h751
                · linarith only [h751, hlam, hphi, ht0b, ht5b, p739_1, u0elo4, u5ehi4]
                · linarith only [h751, hc15, hlam, hphi, ht01, p739_1, u0ehi9]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p739_1, u0ehi9]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                rcases p739_3 (m.d 0 5) (by simp) with h755 | h755
                · linarith only [h755, hlam, hphi, ht0b, ht5b, p739_1, u0elo4, u5ehi1]
                · linarith only [h755, hc25, hlam, hphi, ht01, ht12, p739_1, u0ehi9]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                linarith only [hlam, p739_0]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                linarith only [h687, h738, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p739_1]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                rcases p739_3 (m.d 0 5) (by simp) with h760 | h760
                · linarith only [h760, hlam, hphi, ht0b, ht5b, p739_1, u0elo4, u5ehi4]
                · linarith only [h760, hc25, hlam, hphi, ht01, ht12, p739_1, u0ehi9]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p739_1, u0ehi9]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                rcases p739_3 (m.d 0 5) (by simp) with h764 | h764
                · linarith only [h764, hlam, hphi, ht0b, ht5b, p739_1, u0elo4, u5ehi1]
                · linarith only [h764, hc35, hlam, hphi, ht01, ht12, ht23, p739_1, u0ehi9]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                rcases p739_3 (m.d 0 5) (by simp) with h767 | h767
                · linarith only [h767, hlam, hphi, ht0b, ht5b, p739_1, u0elo4, u5ehi2]
                · linarith only [h767, hc35, hlam, hphi, ht01, ht12, ht23, p739_1, u0ehi9]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                linarith only [hlam, p739_0]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                rcases p739_3 (m.d 0 5) (by simp) with h771 | h771
                · linarith only [h771, hlam, hphi, ht0b, ht5b, p739_1, u0elo4, u5ehi4]
                · linarith only [h771, hc35, hlam, hphi, ht01, ht12, ht23, p739_1, u0ehi9]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p739_1, u0ehi9]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                rcases p739_3 (m.d 0 5) (by simp) with h775 | h775
                · linarith only [h775, hlam, hphi, ht0b, ht5b, p739_1, u0elo4, u5ehi1]
                · linarith only [h775, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p739_1, u0ehi9]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                rcases p739_3 (m.d 0 5) (by simp) with h778 | h778
                · linarith only [h778, hlam, hphi, ht0b, ht5b, p739_1, u0elo4, u5ehi2]
                · linarith only [h778, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p739_1, u0ehi9]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                linarith only [h687, h738, hc23, hc45, hlam, hphi, ht34, p0_1, p739_1]
              · have p739_0 := h739c.1
                have p739_1 := h739c.2.1
                have p739_2 := h739c.2.2.1
                have p739_3 := h739c.2.2.2
                linarith only [hlam, p739_0]
            · linarith only [h685, h738, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
      · linarith only [h686, hlam, p0_0]
    · linarith only [h685, hc13, hlam, hphi, ht01, p0_1, u0ehi7]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 3) (by simp) with h786 | h786
    · linarith only [h786, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
    · linarith only [h786, hc13, hlam, hphi, ht01, p0_1, u0ehi7]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc23, hlam, hphi, ht01, ht12, p0_1, u0ehi7]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 3) (by simp) with h790 | h790
    · rcases p0_3 (m.d 1 3) (by simp) with h791 | h791
      · linarith only [h791, hlam, p0_0]
      · rcases p0_3 (m.d 2 3) (by simp) with h793 | h793
        · rcases p0_3 (m.d 3 4) (by simp) with h794 | h794
          · rcases p0_3 (m.d 3 5) (by simp) with h795 | h795
            · rcases h5bigk with h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                linarith only [hlam, p796_0]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p796_1, u0elo4, u5ehi1]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p796_1, u0elo4, u5ehi2]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                linarith only [h795, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p796_1, u0elo4]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p796_1, u0elo4, u5ehi4]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p796_1, u0ehi9]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                linarith only [hlam, p796_0]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                rcases p796_3 (m.d 0 5) (by simp) with h804 | h804
                · linarith only [h804, hlam, hphi, ht0b, ht5b, p796_1, u0elo4, u5ehi2]
                · linarith only [h804, hc15, hlam, hphi, ht01, p796_1, u0ehi9]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                linarith only [h795, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p796_1]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                rcases p796_3 (m.d 0 5) (by simp) with h808 | h808
                · linarith only [h808, hlam, hphi, ht0b, ht5b, p796_1, u0elo4, u5ehi4]
                · linarith only [h808, hc15, hlam, hphi, ht01, p796_1, u0ehi9]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p796_1, u0ehi9]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                rcases p796_3 (m.d 0 5) (by simp) with h812 | h812
                · linarith only [h812, hlam, hphi, ht0b, ht5b, p796_1, u0elo4, u5ehi1]
                · linarith only [h812, hc25, hlam, hphi, ht01, ht12, p796_1, u0ehi9]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                linarith only [hlam, p796_0]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                linarith only [h795, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p796_1]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                rcases p796_3 (m.d 0 5) (by simp) with h817 | h817
                · linarith only [h817, hlam, hphi, ht0b, ht5b, p796_1, u0elo4, u5ehi4]
                · linarith only [h817, hc25, hlam, hphi, ht01, ht12, p796_1, u0ehi9]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p796_1, u0ehi9]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                rcases p796_3 (m.d 0 5) (by simp) with h821 | h821
                · linarith only [h821, hlam, hphi, ht0b, ht5b, p796_1, u0elo4, u5ehi1]
                · linarith only [h821, hc35, hlam, hphi, ht01, ht12, ht23, p796_1, u0ehi9]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                rcases p796_3 (m.d 0 5) (by simp) with h824 | h824
                · linarith only [h824, hlam, hphi, ht0b, ht5b, p796_1, u0elo4, u5ehi2]
                · linarith only [h824, hc35, hlam, hphi, ht01, ht12, ht23, p796_1, u0ehi9]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                linarith only [hlam, p796_0]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                rcases p796_3 (m.d 0 5) (by simp) with h828 | h828
                · linarith only [h828, hlam, hphi, ht0b, ht5b, p796_1, u0elo4, u5ehi4]
                · linarith only [h828, hc35, hlam, hphi, ht01, ht12, ht23, p796_1, u0ehi9]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p796_1, u0ehi9]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                rcases p796_3 (m.d 0 5) (by simp) with h832 | h832
                · linarith only [h832, hlam, hphi, ht0b, ht5b, p796_1, u0elo4, u5ehi1]
                · linarith only [h832, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p796_1, u0ehi9]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                rcases p796_3 (m.d 0 5) (by simp) with h835 | h835
                · linarith only [h835, hlam, hphi, ht0b, ht5b, p796_1, u0elo4, u5ehi2]
                · linarith only [h835, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p796_1, u0ehi9]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                linarith only [h795, hc13, hc45, hlam, hphi, ht34, p0_1, p796_1]
              · have p796_0 := h796c.1
                have p796_1 := h796c.2.1
                have p796_2 := h796c.2.2.1
                have p796_3 := h796c.2.2.2
                linarith only [hlam, p796_0]
            · linarith only [h790, h795, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
          · rcases p0_3 (m.d 3 5) (by simp) with h841 | h841
            · rcases h5bigk with h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                linarith only [hlam, p842_0]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p842_1, u0elo4, u5ehi1]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p842_1, u0elo4, u5ehi2]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                linarith only [h841, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p842_1, u0elo4]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p842_1, u0elo4, u5ehi4]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p842_1, u0ehi9]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                linarith only [hlam, p842_0]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                rcases p842_3 (m.d 0 5) (by simp) with h850 | h850
                · linarith only [h850, hlam, hphi, ht0b, ht5b, p842_1, u0elo4, u5ehi2]
                · linarith only [h850, hc15, hlam, hphi, ht01, p842_1, u0ehi9]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                linarith only [h841, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p842_1]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                rcases p842_3 (m.d 0 5) (by simp) with h854 | h854
                · linarith only [h854, hlam, hphi, ht0b, ht5b, p842_1, u0elo4, u5ehi4]
                · linarith only [h854, hc15, hlam, hphi, ht01, p842_1, u0ehi9]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p842_1, u0ehi9]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                rcases p842_3 (m.d 0 5) (by simp) with h858 | h858
                · linarith only [h858, hlam, hphi, ht0b, ht5b, p842_1, u0elo4, u5ehi1]
                · linarith only [h858, hc25, hlam, hphi, ht01, ht12, p842_1, u0ehi9]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                linarith only [hlam, p842_0]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                linarith only [h841, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p842_1]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                rcases p842_3 (m.d 0 5) (by simp) with h863 | h863
                · linarith only [h863, hlam, hphi, ht0b, ht5b, p842_1, u0elo4, u5ehi4]
                · linarith only [h863, hc25, hlam, hphi, ht01, ht12, p842_1, u0ehi9]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p842_1, u0ehi9]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                rcases p842_3 (m.d 0 5) (by simp) with h867 | h867
                · linarith only [h867, hlam, hphi, ht0b, ht5b, p842_1, u0elo4, u5ehi1]
                · linarith only [h867, hc35, hlam, hphi, ht01, ht12, ht23, p842_1, u0ehi9]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                rcases p842_3 (m.d 0 5) (by simp) with h870 | h870
                · linarith only [h870, hlam, hphi, ht0b, ht5b, p842_1, u0elo4, u5ehi2]
                · linarith only [h870, hc35, hlam, hphi, ht01, ht12, ht23, p842_1, u0ehi9]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                linarith only [hlam, p842_0]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                rcases p842_3 (m.d 0 5) (by simp) with h874 | h874
                · linarith only [h874, hlam, hphi, ht0b, ht5b, p842_1, u0elo4, u5ehi4]
                · linarith only [h874, hc35, hlam, hphi, ht01, ht12, ht23, p842_1, u0ehi9]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p842_1, u0ehi9]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                rcases p842_3 (m.d 0 5) (by simp) with h878 | h878
                · linarith only [h878, hlam, hphi, ht0b, ht5b, p842_1, u0elo4, u5ehi1]
                · linarith only [h878, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p842_1, u0ehi9]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                rcases p842_3 (m.d 0 5) (by simp) with h881 | h881
                · linarith only [h881, hlam, hphi, ht0b, ht5b, p842_1, u0elo4, u5ehi2]
                · linarith only [h881, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p842_1, u0ehi9]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                linarith only [h841, hc13, hc45, hlam, hphi, ht34, p0_1, p842_1]
              · have p842_0 := h842c.1
                have p842_1 := h842c.2.1
                have p842_2 := h842c.2.2.1
                have p842_3 := h842c.2.2.2
                linarith only [hlam, p842_0]
            · linarith only [h790, h841, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
        · linarith only [h793, hlam, p0_0]
    · linarith only [h790, hc23, hlam, hphi, ht01, ht12, p0_1, u0ehi7]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 3) (by simp) with h890 | h890
    · rcases p0_3 (m.d 1 3) (by simp) with h891 | h891
      · rcases p0_3 (m.d 2 3) (by simp) with h892 | h892
        · rcases p0_3 (m.d 3 4) (by simp) with h893 | h893
          · linarith only [h893, hlam, p0_0]
          · rcases p0_3 (m.d 3 5) (by simp) with h895 | h895
            · rcases h5bigk with h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                linarith only [hlam, p896_0]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p896_1, u0elo4, u5ehi1]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p896_1, u0elo4, u5ehi2]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                linarith only [h895, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, p896_1, u0elo4]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p896_1, u0elo4, u5ehi4]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p896_1, u0ehi9]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                linarith only [hlam, p896_0]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                rcases p896_3 (m.d 0 5) (by simp) with h904 | h904
                · linarith only [h904, hlam, hphi, ht0b, ht5b, p896_1, u0elo4, u5ehi2]
                · linarith only [h904, hc15, hlam, hphi, ht01, p896_1, u0ehi9]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                linarith only [h895, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, p896_1]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                rcases p896_3 (m.d 0 5) (by simp) with h908 | h908
                · linarith only [h908, hlam, hphi, ht0b, ht5b, p896_1, u0elo4, u5ehi4]
                · linarith only [h908, hc15, hlam, hphi, ht01, p896_1, u0ehi9]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p896_1, u0ehi9]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                rcases p896_3 (m.d 0 5) (by simp) with h912 | h912
                · linarith only [h912, hlam, hphi, ht0b, ht5b, p896_1, u0elo4, u5ehi1]
                · linarith only [h912, hc25, hlam, hphi, ht01, ht12, p896_1, u0ehi9]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                linarith only [hlam, p896_0]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                linarith only [h895, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, p896_1]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                rcases p896_3 (m.d 0 5) (by simp) with h917 | h917
                · linarith only [h917, hlam, hphi, ht0b, ht5b, p896_1, u0elo4, u5ehi4]
                · linarith only [h917, hc25, hlam, hphi, ht01, ht12, p896_1, u0ehi9]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p896_1, u0ehi9]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                rcases p896_3 (m.d 0 5) (by simp) with h921 | h921
                · linarith only [h921, hlam, hphi, ht0b, ht5b, p896_1, u0elo4, u5ehi1]
                · linarith only [h921, hc35, hlam, hphi, ht01, ht12, ht23, p896_1, u0ehi9]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                rcases p896_3 (m.d 0 5) (by simp) with h924 | h924
                · linarith only [h924, hlam, hphi, ht0b, ht5b, p896_1, u0elo4, u5ehi2]
                · linarith only [h924, hc35, hlam, hphi, ht01, ht12, ht23, p896_1, u0ehi9]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                linarith only [hlam, p896_0]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                rcases p896_3 (m.d 0 5) (by simp) with h928 | h928
                · linarith only [h928, hlam, hphi, ht0b, ht5b, p896_1, u0elo4, u5ehi4]
                · linarith only [h928, hc35, hlam, hphi, ht01, ht12, ht23, p896_1, u0ehi9]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p896_1, u0ehi9]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                rcases p896_3 (m.d 0 5) (by simp) with h932 | h932
                · linarith only [h932, hlam, hphi, ht0b, ht5b, p896_1, u0elo4, u5ehi1]
                · linarith only [h932, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p896_1, u0ehi9]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                rcases p896_3 (m.d 0 5) (by simp) with h935 | h935
                · linarith only [h935, hlam, hphi, ht0b, ht5b, p896_1, u0elo4, u5ehi2]
                · linarith only [h935, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p896_1, u0ehi9]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                linarith only [h895, hc34, hc45, hlam, hphi, p0_1, p896_1]
              · have p896_0 := h896c.1
                have p896_1 := h896c.2.1
                have p896_2 := h896c.2.2.1
                have p896_3 := h896c.2.2.2
                linarith only [hlam, p896_0]
            · linarith only [h890, h895, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
        · linarith only [h892, hlam, p0_0]
      · rcases p0_3 (m.d 2 3) (by simp) with h942 | h942
        · rcases p0_3 (m.d 3 4) (by simp) with h943 | h943
          · linarith only [h943, hlam, p0_0]
          · rcases p0_3 (m.d 3 5) (by simp) with h945 | h945
            · rcases h5bigk with h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                linarith only [hlam, p946_0]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p946_1, u0elo4, u5ehi1]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p946_1, u0elo4, u5ehi2]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                linarith only [h891, h945, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p946_1, u0elo4]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p946_1, u0elo4, u5ehi4]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p946_1, u0ehi9]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                linarith only [hlam, p946_0]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                rcases p946_3 (m.d 0 5) (by simp) with h954 | h954
                · linarith only [h954, hlam, hphi, ht0b, ht5b, p946_1, u0elo4, u5ehi2]
                · linarith only [h954, hc15, hlam, hphi, ht01, p946_1, u0ehi9]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                linarith only [h891, h945, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p946_1]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                rcases p946_3 (m.d 0 5) (by simp) with h958 | h958
                · linarith only [h958, hlam, hphi, ht0b, ht5b, p946_1, u0elo4, u5ehi4]
                · linarith only [h958, hc15, hlam, hphi, ht01, p946_1, u0ehi9]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p946_1, u0ehi9]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                rcases p946_3 (m.d 0 5) (by simp) with h962 | h962
                · linarith only [h962, hlam, hphi, ht0b, ht5b, p946_1, u0elo4, u5ehi1]
                · linarith only [h962, hc25, hlam, hphi, ht01, ht12, p946_1, u0ehi9]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                linarith only [hlam, p946_0]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                linarith only [h891, h945, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p946_1]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                rcases p946_3 (m.d 0 5) (by simp) with h967 | h967
                · linarith only [h967, hlam, hphi, ht0b, ht5b, p946_1, u0elo4, u5ehi4]
                · linarith only [h967, hc25, hlam, hphi, ht01, ht12, p946_1, u0ehi9]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p946_1, u0ehi9]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                rcases p946_3 (m.d 0 5) (by simp) with h971 | h971
                · linarith only [h971, hlam, hphi, ht0b, ht5b, p946_1, u0elo4, u5ehi1]
                · linarith only [h971, hc35, hlam, hphi, ht01, ht12, ht23, p946_1, u0ehi9]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                rcases p946_3 (m.d 0 5) (by simp) with h974 | h974
                · linarith only [h974, hlam, hphi, ht0b, ht5b, p946_1, u0elo4, u5ehi2]
                · linarith only [h974, hc35, hlam, hphi, ht01, ht12, ht23, p946_1, u0ehi9]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                linarith only [hlam, p946_0]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                rcases p946_3 (m.d 0 5) (by simp) with h978 | h978
                · linarith only [h978, hlam, hphi, ht0b, ht5b, p946_1, u0elo4, u5ehi4]
                · linarith only [h978, hc35, hlam, hphi, ht01, ht12, ht23, p946_1, u0ehi9]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p946_1, u0ehi9]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                rcases p946_3 (m.d 0 5) (by simp) with h982 | h982
                · linarith only [h982, hlam, hphi, ht0b, ht5b, p946_1, u0elo4, u5ehi1]
                · linarith only [h982, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p946_1, u0ehi9]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                rcases p946_3 (m.d 0 5) (by simp) with h985 | h985
                · linarith only [h985, hlam, hphi, ht0b, ht5b, p946_1, u0elo4, u5ehi2]
                · linarith only [h985, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p946_1, u0ehi9]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                linarith only [h891, h945, hc13, hc45, hlam, hphi, ht34, p0_1, p946_1]
              · have p946_0 := h946c.1
                have p946_1 := h946c.2.1
                have p946_2 := h946c.2.2.1
                have p946_3 := h946c.2.2.2
                linarith only [hlam, p946_0]
            · linarith only [h890, h945, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
        · linarith only [h942, hlam, p0_0]
    · linarith only [h890, hc23, hlam, hphi, ht01, ht12, p0_1, u0ehi7]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 3) (by simp) with h993 | h993
    · linarith only [h993, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
    · linarith only [h993, hc23, hlam, hphi, ht01, ht12, p0_1, u0ehi7]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi7]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 3) (by simp) with h997 | h997
    · rcases p0_3 (m.d 1 3) (by simp) with h998 | h998
      · linarith only [h998, hlam, p0_0]
      · rcases p0_3 (m.d 2 3) (by simp) with h1000 | h1000
        · rcases p0_3 (m.d 3 4) (by simp) with h1001 | h1001
          · rcases p0_3 (m.d 3 5) (by simp) with h1002 | h1002
            · rcases h5bigk with h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                linarith only [hlam, p1003_0]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1003_1, u0elo4, u5ehi1]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1003_1, u0elo4, u5ehi2]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                linarith only [h1002, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1003_1, u0elo4]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1003_1, u0elo4, u5ehi4]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p1003_1, u0ehi9]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                linarith only [hlam, p1003_0]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                rcases p1003_3 (m.d 0 5) (by simp) with h1011 | h1011
                · linarith only [h1011, hlam, hphi, ht0b, ht5b, p1003_1, u0elo4, u5ehi2]
                · linarith only [h1011, hc15, hlam, hphi, ht01, p1003_1, u0ehi9]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                linarith only [h1002, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p1003_1]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                rcases p1003_3 (m.d 0 5) (by simp) with h1015 | h1015
                · linarith only [h1015, hlam, hphi, ht0b, ht5b, p1003_1, u0elo4, u5ehi4]
                · linarith only [h1015, hc15, hlam, hphi, ht01, p1003_1, u0ehi9]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p1003_1, u0ehi9]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                rcases p1003_3 (m.d 0 5) (by simp) with h1019 | h1019
                · linarith only [h1019, hlam, hphi, ht0b, ht5b, p1003_1, u0elo4, u5ehi1]
                · linarith only [h1019, hc25, hlam, hphi, ht01, ht12, p1003_1, u0ehi9]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                linarith only [hlam, p1003_0]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                linarith only [h1002, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p1003_1]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                rcases p1003_3 (m.d 0 5) (by simp) with h1024 | h1024
                · linarith only [h1024, hlam, hphi, ht0b, ht5b, p1003_1, u0elo4, u5ehi4]
                · linarith only [h1024, hc25, hlam, hphi, ht01, ht12, p1003_1, u0ehi9]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p1003_1, u0ehi9]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                rcases p1003_3 (m.d 0 5) (by simp) with h1028 | h1028
                · linarith only [h1028, hlam, hphi, ht0b, ht5b, p1003_1, u0elo4, u5ehi1]
                · linarith only [h1028, hc35, hlam, hphi, ht01, ht12, ht23, p1003_1, u0ehi9]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                rcases p1003_3 (m.d 0 5) (by simp) with h1031 | h1031
                · linarith only [h1031, hlam, hphi, ht0b, ht5b, p1003_1, u0elo4, u5ehi2]
                · linarith only [h1031, hc35, hlam, hphi, ht01, ht12, ht23, p1003_1, u0ehi9]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                linarith only [hlam, p1003_0]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                rcases p1003_3 (m.d 0 5) (by simp) with h1035 | h1035
                · linarith only [h1035, hlam, hphi, ht0b, ht5b, p1003_1, u0elo4, u5ehi4]
                · linarith only [h1035, hc35, hlam, hphi, ht01, ht12, ht23, p1003_1, u0ehi9]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1003_1, u0ehi9]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                rcases p1003_3 (m.d 0 5) (by simp) with h1039 | h1039
                · linarith only [h1039, hlam, hphi, ht0b, ht5b, p1003_1, u0elo4, u5ehi1]
                · linarith only [h1039, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1003_1, u0ehi9]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                rcases p1003_3 (m.d 0 5) (by simp) with h1042 | h1042
                · linarith only [h1042, hlam, hphi, ht0b, ht5b, p1003_1, u0elo4, u5ehi2]
                · linarith only [h1042, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1003_1, u0ehi9]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                linarith only [h1002, hc13, hc45, hlam, hphi, ht34, p0_1, p1003_1]
              · have p1003_0 := h1003c.1
                have p1003_1 := h1003c.2.1
                have p1003_2 := h1003c.2.2.1
                have p1003_3 := h1003c.2.2.2
                linarith only [hlam, p1003_0]
            · linarith only [h1002, h997, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
          · linarith only [h1001, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h1049 | h1049
          · rcases p0_3 (m.d 3 5) (by simp) with h1050 | h1050
            · rcases h5bigk with h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                linarith only [hlam, p1051_0]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1051_1, u0elo4, u5ehi1]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1051_1, u0elo4, u5ehi2]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                linarith only [h1050, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1051_1, u0elo4]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1051_1, u0elo4, u5ehi4]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p1051_1, u0ehi9]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                linarith only [hlam, p1051_0]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                rcases p1051_3 (m.d 0 5) (by simp) with h1059 | h1059
                · linarith only [h1059, hlam, hphi, ht0b, ht5b, p1051_1, u0elo4, u5ehi2]
                · linarith only [h1059, hc15, hlam, hphi, ht01, p1051_1, u0ehi9]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                linarith only [h1050, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p1051_1]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                rcases p1051_3 (m.d 0 5) (by simp) with h1063 | h1063
                · linarith only [h1063, hlam, hphi, ht0b, ht5b, p1051_1, u0elo4, u5ehi4]
                · linarith only [h1063, hc15, hlam, hphi, ht01, p1051_1, u0ehi9]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p1051_1, u0ehi9]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                rcases p1051_3 (m.d 0 5) (by simp) with h1067 | h1067
                · linarith only [h1067, hlam, hphi, ht0b, ht5b, p1051_1, u0elo4, u5ehi1]
                · linarith only [h1067, hc25, hlam, hphi, ht01, ht12, p1051_1, u0ehi9]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                linarith only [hlam, p1051_0]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                linarith only [h1050, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p1051_1]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                rcases p1051_3 (m.d 0 5) (by simp) with h1072 | h1072
                · linarith only [h1072, hlam, hphi, ht0b, ht5b, p1051_1, u0elo4, u5ehi4]
                · linarith only [h1072, hc25, hlam, hphi, ht01, ht12, p1051_1, u0ehi9]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p1051_1, u0ehi9]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                rcases p1051_3 (m.d 0 5) (by simp) with h1076 | h1076
                · linarith only [h1076, hlam, hphi, ht0b, ht5b, p1051_1, u0elo4, u5ehi1]
                · linarith only [h1076, hc35, hlam, hphi, ht01, ht12, ht23, p1051_1, u0ehi9]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                rcases p1051_3 (m.d 0 5) (by simp) with h1079 | h1079
                · linarith only [h1079, hlam, hphi, ht0b, ht5b, p1051_1, u0elo4, u5ehi2]
                · linarith only [h1079, hc35, hlam, hphi, ht01, ht12, ht23, p1051_1, u0ehi9]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                linarith only [hlam, p1051_0]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                rcases p1051_3 (m.d 0 5) (by simp) with h1083 | h1083
                · linarith only [h1083, hlam, hphi, ht0b, ht5b, p1051_1, u0elo4, u5ehi4]
                · linarith only [h1083, hc35, hlam, hphi, ht01, ht12, ht23, p1051_1, u0ehi9]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1051_1, u0ehi9]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                rcases p1051_3 (m.d 0 5) (by simp) with h1087 | h1087
                · linarith only [h1087, hlam, hphi, ht0b, ht5b, p1051_1, u0elo4, u5ehi1]
                · linarith only [h1087, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1051_1, u0ehi9]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                rcases p1051_3 (m.d 0 5) (by simp) with h1090 | h1090
                · linarith only [h1090, hlam, hphi, ht0b, ht5b, p1051_1, u0elo4, u5ehi2]
                · linarith only [h1090, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1051_1, u0ehi9]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                linarith only [h1050, hc13, hc45, hlam, hphi, ht34, p0_1, p1051_1]
              · have p1051_0 := h1051c.1
                have p1051_1 := h1051c.2.1
                have p1051_2 := h1051c.2.2.1
                have p1051_3 := h1051c.2.2.2
                linarith only [hlam, p1051_0]
            · linarith only [h1050, h997, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
          · linarith only [h1049, hlam, p0_0]
    · linarith only [h997, hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi7]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 3) (by simp) with h1098 | h1098
    · rcases p0_3 (m.d 1 3) (by simp) with h1099 | h1099
      · rcases p0_3 (m.d 2 3) (by simp) with h1100 | h1100
        · linarith only [h1100, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h1102 | h1102
          · rcases p0_3 (m.d 3 5) (by simp) with h1103 | h1103
            · rcases h5bigk with h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                linarith only [hlam, p1104_0]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1104_1, u0elo4, u5ehi1]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1104_1, u0elo4, u5ehi2]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                linarith only [h1103, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1104_1, u0elo4]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1104_1, u0elo4, u5ehi4]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p1104_1, u0ehi9]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                linarith only [hlam, p1104_0]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                rcases p1104_3 (m.d 0 5) (by simp) with h1112 | h1112
                · linarith only [h1112, hlam, hphi, ht0b, ht5b, p1104_1, u0elo4, u5ehi2]
                · linarith only [h1112, hc15, hlam, hphi, ht01, p1104_1, u0ehi9]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                linarith only [h1103, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p1104_1]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                rcases p1104_3 (m.d 0 5) (by simp) with h1116 | h1116
                · linarith only [h1116, hlam, hphi, ht0b, ht5b, p1104_1, u0elo4, u5ehi4]
                · linarith only [h1116, hc15, hlam, hphi, ht01, p1104_1, u0ehi9]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p1104_1, u0ehi9]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                rcases p1104_3 (m.d 0 5) (by simp) with h1120 | h1120
                · linarith only [h1120, hlam, hphi, ht0b, ht5b, p1104_1, u0elo4, u5ehi1]
                · linarith only [h1120, hc25, hlam, hphi, ht01, ht12, p1104_1, u0ehi9]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                linarith only [hlam, p1104_0]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                linarith only [h1103, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p1104_1]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                rcases p1104_3 (m.d 0 5) (by simp) with h1125 | h1125
                · linarith only [h1125, hlam, hphi, ht0b, ht5b, p1104_1, u0elo4, u5ehi4]
                · linarith only [h1125, hc25, hlam, hphi, ht01, ht12, p1104_1, u0ehi9]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p1104_1, u0ehi9]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                rcases p1104_3 (m.d 0 5) (by simp) with h1129 | h1129
                · linarith only [h1129, hlam, hphi, ht0b, ht5b, p1104_1, u0elo4, u5ehi1]
                · linarith only [h1129, hc35, hlam, hphi, ht01, ht12, ht23, p1104_1, u0ehi9]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                rcases p1104_3 (m.d 0 5) (by simp) with h1132 | h1132
                · linarith only [h1132, hlam, hphi, ht0b, ht5b, p1104_1, u0elo4, u5ehi2]
                · linarith only [h1132, hc35, hlam, hphi, ht01, ht12, ht23, p1104_1, u0ehi9]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                linarith only [hlam, p1104_0]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                rcases p1104_3 (m.d 0 5) (by simp) with h1136 | h1136
                · linarith only [h1136, hlam, hphi, ht0b, ht5b, p1104_1, u0elo4, u5ehi4]
                · linarith only [h1136, hc35, hlam, hphi, ht01, ht12, ht23, p1104_1, u0ehi9]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1104_1, u0ehi9]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                rcases p1104_3 (m.d 0 5) (by simp) with h1140 | h1140
                · linarith only [h1140, hlam, hphi, ht0b, ht5b, p1104_1, u0elo4, u5ehi1]
                · linarith only [h1140, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1104_1, u0ehi9]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                rcases p1104_3 (m.d 0 5) (by simp) with h1143 | h1143
                · linarith only [h1143, hlam, hphi, ht0b, ht5b, p1104_1, u0elo4, u5ehi2]
                · linarith only [h1143, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1104_1, u0ehi9]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                linarith only [h1103, hc23, hc45, hlam, hphi, ht34, p0_1, p1104_1]
              · have p1104_0 := h1104c.1
                have p1104_1 := h1104c.2.1
                have p1104_2 := h1104c.2.2.1
                have p1104_3 := h1104c.2.2.2
                linarith only [hlam, p1104_0]
            · linarith only [h1098, h1103, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
          · linarith only [h1102, hlam, p0_0]
      · rcases p0_3 (m.d 2 3) (by simp) with h1150 | h1150
        · linarith only [h1150, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h1152 | h1152
          · rcases p0_3 (m.d 3 5) (by simp) with h1153 | h1153
            · rcases h5bigk with h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                linarith only [hlam, p1154_0]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1154_1, u0elo4, u5ehi1]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1154_1, u0elo4, u5ehi2]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                linarith only [h1099, h1153, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1154_1, u0elo4]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1154_1, u0elo4, u5ehi4]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p1154_1, u0ehi9]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                linarith only [hlam, p1154_0]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                rcases p1154_3 (m.d 0 5) (by simp) with h1162 | h1162
                · linarith only [h1162, hlam, hphi, ht0b, ht5b, p1154_1, u0elo4, u5ehi2]
                · linarith only [h1162, hc15, hlam, hphi, ht01, p1154_1, u0ehi9]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                linarith only [h1099, h1153, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p1154_1]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                rcases p1154_3 (m.d 0 5) (by simp) with h1166 | h1166
                · linarith only [h1166, hlam, hphi, ht0b, ht5b, p1154_1, u0elo4, u5ehi4]
                · linarith only [h1166, hc15, hlam, hphi, ht01, p1154_1, u0ehi9]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p1154_1, u0ehi9]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                rcases p1154_3 (m.d 0 5) (by simp) with h1170 | h1170
                · linarith only [h1170, hlam, hphi, ht0b, ht5b, p1154_1, u0elo4, u5ehi1]
                · linarith only [h1170, hc25, hlam, hphi, ht01, ht12, p1154_1, u0ehi9]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                linarith only [hlam, p1154_0]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                linarith only [h1099, h1153, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p1154_1]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                rcases p1154_3 (m.d 0 5) (by simp) with h1175 | h1175
                · linarith only [h1175, hlam, hphi, ht0b, ht5b, p1154_1, u0elo4, u5ehi4]
                · linarith only [h1175, hc25, hlam, hphi, ht01, ht12, p1154_1, u0ehi9]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p1154_1, u0ehi9]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                rcases p1154_3 (m.d 0 5) (by simp) with h1179 | h1179
                · linarith only [h1179, hlam, hphi, ht0b, ht5b, p1154_1, u0elo4, u5ehi1]
                · linarith only [h1179, hc35, hlam, hphi, ht01, ht12, ht23, p1154_1, u0ehi9]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                rcases p1154_3 (m.d 0 5) (by simp) with h1182 | h1182
                · linarith only [h1182, hlam, hphi, ht0b, ht5b, p1154_1, u0elo4, u5ehi2]
                · linarith only [h1182, hc35, hlam, hphi, ht01, ht12, ht23, p1154_1, u0ehi9]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                linarith only [hlam, p1154_0]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                rcases p1154_3 (m.d 0 5) (by simp) with h1186 | h1186
                · linarith only [h1186, hlam, hphi, ht0b, ht5b, p1154_1, u0elo4, u5ehi4]
                · linarith only [h1186, hc35, hlam, hphi, ht01, ht12, ht23, p1154_1, u0ehi9]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1154_1, u0ehi9]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                rcases p1154_3 (m.d 0 5) (by simp) with h1190 | h1190
                · linarith only [h1190, hlam, hphi, ht0b, ht5b, p1154_1, u0elo4, u5ehi1]
                · linarith only [h1190, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1154_1, u0ehi9]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                rcases p1154_3 (m.d 0 5) (by simp) with h1193 | h1193
                · linarith only [h1193, hlam, hphi, ht0b, ht5b, p1154_1, u0elo4, u5ehi2]
                · linarith only [h1193, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1154_1, u0ehi9]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                linarith only [h1099, h1153, hc13, hc45, hlam, hphi, ht34, p0_1, p1154_1]
              · have p1154_0 := h1154c.1
                have p1154_1 := h1154c.2.1
                have p1154_2 := h1154c.2.2.1
                have p1154_3 := h1154c.2.2.2
                linarith only [hlam, p1154_0]
            · linarith only [h1098, h1153, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
          · linarith only [h1152, hlam, p0_0]
    · linarith only [h1098, hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi7]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 3) (by simp) with h1202 | h1202
    · linarith only [h1202, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi3]
    · linarith only [h1202, hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi7]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi7]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 3) (by simp) with h1206 | h1206
    · rcases p0_3 (m.d 1 3) (by simp) with h1207 | h1207
      · linarith only [h1207, hlam, p0_0]
      · rcases p0_3 (m.d 2 3) (by simp) with h1209 | h1209
        · rcases p0_3 (m.d 3 4) (by simp) with h1210 | h1210
          · rcases p0_3 (m.d 3 5) (by simp) with h1211 | h1211
            · rcases h5bigk with h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, p1212_0]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1212_1, u0elo4, u5ehi1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1212_1, u0elo4, u5ehi2]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1212_1, u0elo4]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1212_1, u0elo4, u5ehi4]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p1212_1, u0ehi9]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, p1212_0]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                rcases p1212_3 (m.d 0 5) (by simp) with h1220 | h1220
                · linarith only [h1220, hlam, hphi, ht0b, ht5b, p1212_1, u0elo4, u5ehi2]
                · linarith only [h1220, hc15, hlam, hphi, ht01, p1212_1, u0ehi9]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p1212_1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                rcases p1212_3 (m.d 0 5) (by simp) with h1224 | h1224
                · linarith only [h1224, hlam, hphi, ht0b, ht5b, p1212_1, u0elo4, u5ehi4]
                · linarith only [h1224, hc15, hlam, hphi, ht01, p1212_1, u0ehi9]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p1212_1, u0ehi9]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                rcases p1212_3 (m.d 0 5) (by simp) with h1228 | h1228
                · linarith only [h1228, hlam, hphi, ht0b, ht5b, p1212_1, u0elo4, u5ehi1]
                · linarith only [h1228, hc25, hlam, hphi, ht01, ht12, p1212_1, u0ehi9]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, p1212_0]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p1212_1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                rcases p1212_3 (m.d 0 5) (by simp) with h1233 | h1233
                · linarith only [h1233, hlam, hphi, ht0b, ht5b, p1212_1, u0elo4, u5ehi4]
                · linarith only [h1233, hc25, hlam, hphi, ht01, ht12, p1212_1, u0ehi9]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1206, hlam, hphi, p1212_1, u0ehi9, u0elo2]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1206, hlam, hphi, ht0b, ht5b, p1212_1, u0elo2, u5ehi1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1206, hlam, hphi, ht0b, ht5b, p1212_1, u0elo2, u5ehi2]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, p1212_0]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1206, hlam, hphi, ht0b, ht5b, p1212_1, u0elo2, u5ehi4]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1212_1, u0ehi9]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                rcases p1212_3 (m.d 0 5) (by simp) with h1242 | h1242
                · linarith only [h1242, hlam, hphi, ht0b, ht5b, p1212_1, u0elo4, u5ehi1]
                · linarith only [h1242, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1212_1, u0ehi9]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                rcases p1212_3 (m.d 0 5) (by simp) with h1245 | h1245
                · linarith only [h1245, hlam, hphi, ht0b, ht5b, p1212_1, u0elo4, u5ehi2]
                · linarith only [h1245, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1212_1, u0ehi9]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc13, hc45, hlam, hphi, ht34, p0_1, p1212_1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, p1212_0]
            · linarith only [h1211, hlam, p0_0]
          · rcases p0_3 (m.d 3 5) (by simp) with h1251 | h1251
            · rcases h5bigk with h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [hlam, p1252_0]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1252_1, u0elo4, u5ehi1]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1252_1, u0elo4, u5ehi2]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1252_1, u0elo4]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1252_1, u0elo4, u5ehi4]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p1252_1, u0ehi9]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [hlam, p1252_0]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                rcases p1252_3 (m.d 0 5) (by simp) with h1260 | h1260
                · linarith only [h1260, hlam, hphi, ht0b, ht5b, p1252_1, u0elo4, u5ehi2]
                · linarith only [h1260, hc15, hlam, hphi, ht01, p1252_1, u0ehi9]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p1252_1]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                rcases p1252_3 (m.d 0 5) (by simp) with h1264 | h1264
                · linarith only [h1264, hlam, hphi, ht0b, ht5b, p1252_1, u0elo4, u5ehi4]
                · linarith only [h1264, hc15, hlam, hphi, ht01, p1252_1, u0ehi9]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p1252_1, u0ehi9]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                rcases p1252_3 (m.d 0 5) (by simp) with h1268 | h1268
                · linarith only [h1268, hlam, hphi, ht0b, ht5b, p1252_1, u0elo4, u5ehi1]
                · linarith only [h1268, hc25, hlam, hphi, ht01, ht12, p1252_1, u0ehi9]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [hlam, p1252_0]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p1252_1]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                rcases p1252_3 (m.d 0 5) (by simp) with h1273 | h1273
                · linarith only [h1273, hlam, hphi, ht0b, ht5b, p1252_1, u0elo4, u5ehi4]
                · linarith only [h1273, hc25, hlam, hphi, ht01, ht12, p1252_1, u0ehi9]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p1252_1, u0ehi9]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [h1206, hlam, hphi, ht0b, ht5b, p1252_1, u0elo2, u5ehi1]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [h1206, hlam, hphi, ht0b, ht5b, p1252_1, u0elo2, u5ehi2]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [hlam, p1252_0]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [h1206, hlam, hphi, ht0b, ht5b, p1252_1, u0elo2, u5ehi4]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1252_1, u0ehi9]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                rcases p1252_3 (m.d 0 5) (by simp) with h1282 | h1282
                · linarith only [h1282, hlam, hphi, ht0b, ht5b, p1252_1, u0elo4, u5ehi1]
                · linarith only [h1282, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1252_1, u0ehi9]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                rcases p1252_3 (m.d 0 5) (by simp) with h1285 | h1285
                · linarith only [h1285, hlam, hphi, ht0b, ht5b, p1252_1, u0elo4, u5ehi2]
                · linarith only [h1285, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1252_1, u0ehi9]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [hc13, hc45, hlam, hphi, ht34, p0_1, p1252_1]
              · have p1252_0 := h1252c.1
                have p1252_1 := h1252c.2.1
                have p1252_2 := h1252c.2.2.1
                have p1252_3 := h1252c.2.2.2
                linarith only [hlam, p1252_0]
            · linarith only [h1251, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h1291 | h1291
          · rcases p0_3 (m.d 3 5) (by simp) with h1292 | h1292
            · rcases h5bigk with h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c | h1293c
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [hlam, p1293_0]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1293_1, u0elo4, u5ehi1]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1293_1, u0elo4, u5ehi2]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1293_1, u0elo4]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1293_1, u0elo4, u5ehi4]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p1293_1, u0ehi9]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [hlam, p1293_0]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                rcases p1293_3 (m.d 0 5) (by simp) with h1301 | h1301
                · linarith only [h1301, hlam, hphi, ht0b, ht5b, p1293_1, u0elo4, u5ehi2]
                · linarith only [h1301, hc15, hlam, hphi, ht01, p1293_1, u0ehi9]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p1293_1]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                rcases p1293_3 (m.d 0 5) (by simp) with h1305 | h1305
                · linarith only [h1305, hlam, hphi, ht0b, ht5b, p1293_1, u0elo4, u5ehi4]
                · linarith only [h1305, hc15, hlam, hphi, ht01, p1293_1, u0ehi9]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p1293_1, u0ehi9]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                rcases p1293_3 (m.d 0 5) (by simp) with h1309 | h1309
                · linarith only [h1309, hlam, hphi, ht0b, ht5b, p1293_1, u0elo4, u5ehi1]
                · linarith only [h1309, hc25, hlam, hphi, ht01, ht12, p1293_1, u0ehi9]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [hlam, p1293_0]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p1293_1]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                rcases p1293_3 (m.d 0 5) (by simp) with h1314 | h1314
                · linarith only [h1314, hlam, hphi, ht0b, ht5b, p1293_1, u0elo4, u5ehi4]
                · linarith only [h1314, hc25, hlam, hphi, ht01, ht12, p1293_1, u0ehi9]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [h1291, hc34, hlam, hphi, ht01, ht12, ht23, p1293_1, u0ehi9]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [h1206, hlam, hphi, ht0b, ht5b, p1293_1, u0elo2, u5ehi1]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [h1206, hlam, hphi, ht0b, ht5b, p1293_1, u0elo2, u5ehi2]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [hlam, p1293_0]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [h1206, hlam, hphi, ht0b, ht5b, p1293_1, u0elo2, u5ehi4]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1293_1, u0ehi9]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                rcases p1293_3 (m.d 0 5) (by simp) with h1323 | h1323
                · linarith only [h1323, hlam, hphi, ht0b, ht5b, p1293_1, u0elo4, u5ehi1]
                · linarith only [h1323, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1293_1, u0ehi9]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                rcases p1293_3 (m.d 0 5) (by simp) with h1326 | h1326
                · linarith only [h1326, hlam, hphi, ht0b, ht5b, p1293_1, u0elo4, u5ehi2]
                · linarith only [h1326, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1293_1, u0ehi9]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [hc13, hc45, hlam, hphi, ht34, p0_1, p1293_1]
              · have p1293_0 := h1293c.1
                have p1293_1 := h1293c.2.1
                have p1293_2 := h1293c.2.2.1
                have p1293_3 := h1293c.2.2.2
                linarith only [hlam, p1293_0]
            · linarith only [h1292, hlam, p0_0]
          · rcases p0_3 (m.d 3 5) (by simp) with h1332 | h1332
            · rcases h5bigk with h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hlam, p1333_0]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1333_1, u0elo4, u5ehi1]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1333_1, u0elo4, u5ehi2]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1333_1, u0elo4]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1333_1, u0elo4, u5ehi4]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p1333_1, u0ehi9]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hlam, p1333_0]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                rcases p1333_3 (m.d 0 5) (by simp) with h1341 | h1341
                · linarith only [h1341, hlam, hphi, ht0b, ht5b, p1333_1, u0elo4, u5ehi2]
                · linarith only [h1341, hc15, hlam, hphi, ht01, p1333_1, u0ehi9]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p1333_1]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                rcases p1333_3 (m.d 0 5) (by simp) with h1345 | h1345
                · linarith only [h1345, hlam, hphi, ht0b, ht5b, p1333_1, u0elo4, u5ehi4]
                · linarith only [h1345, hc15, hlam, hphi, ht01, p1333_1, u0ehi9]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p1333_1, u0ehi9]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                rcases p1333_3 (m.d 0 5) (by simp) with h1349 | h1349
                · linarith only [h1349, hlam, hphi, ht0b, ht5b, p1333_1, u0elo4, u5ehi1]
                · linarith only [h1349, hc25, hlam, hphi, ht01, ht12, p1333_1, u0ehi9]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hlam, p1333_0]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p1333_1]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                rcases p1333_3 (m.d 0 5) (by simp) with h1354 | h1354
                · linarith only [h1354, hlam, hphi, ht0b, ht5b, p1333_1, u0elo4, u5ehi4]
                · linarith only [h1354, hc25, hlam, hphi, ht01, ht12, p1333_1, u0ehi9]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p1333_1, u0ehi9]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [h1206, hlam, hphi, ht0b, ht5b, p1333_1, u0elo2, u5ehi1]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [h1206, hlam, hphi, ht0b, ht5b, p1333_1, u0elo2, u5ehi2]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hlam, p1333_0]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [h1206, hlam, hphi, ht0b, ht5b, p1333_1, u0elo2, u5ehi4]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1333_1, u0ehi9]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                rcases p1333_3 (m.d 0 5) (by simp) with h1363 | h1363
                · linarith only [h1363, hlam, hphi, ht0b, ht5b, p1333_1, u0elo4, u5ehi1]
                · linarith only [h1363, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1333_1, u0ehi9]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                rcases p1333_3 (m.d 0 5) (by simp) with h1366 | h1366
                · linarith only [h1366, hlam, hphi, ht0b, ht5b, p1333_1, u0elo4, u5ehi2]
                · linarith only [h1366, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1333_1, u0ehi9]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc13, hc45, hlam, hphi, ht34, p0_1, p1333_1]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hlam, p1333_0]
            · linarith only [h1332, hlam, p0_0]
    · linarith only [h1206, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi7]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 3) (by simp) with h1373 | h1373
    · rcases p0_3 (m.d 1 3) (by simp) with h1374 | h1374
      · rcases p0_3 (m.d 2 3) (by simp) with h1375 | h1375
        · linarith only [h1375, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h1377 | h1377
          · rcases p0_3 (m.d 3 5) (by simp) with h1378 | h1378
            · rcases h5bigk with h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [hlam, p1379_0]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1379_1, u0elo4, u5ehi1]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1379_1, u0elo4, u5ehi2]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1379_1, u0elo4]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1379_1, u0elo4, u5ehi4]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p1379_1, u0ehi9]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [hlam, p1379_0]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                rcases p1379_3 (m.d 0 5) (by simp) with h1387 | h1387
                · linarith only [h1387, hlam, hphi, ht0b, ht5b, p1379_1, u0elo4, u5ehi2]
                · linarith only [h1387, hc15, hlam, hphi, ht01, p1379_1, u0ehi9]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p1379_1]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                rcases p1379_3 (m.d 0 5) (by simp) with h1391 | h1391
                · linarith only [h1391, hlam, hphi, ht0b, ht5b, p1379_1, u0elo4, u5ehi4]
                · linarith only [h1391, hc15, hlam, hphi, ht01, p1379_1, u0ehi9]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p1379_1, u0ehi9]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                rcases p1379_3 (m.d 0 5) (by simp) with h1395 | h1395
                · linarith only [h1395, hlam, hphi, ht0b, ht5b, p1379_1, u0elo4, u5ehi1]
                · linarith only [h1395, hc25, hlam, hphi, ht01, ht12, p1379_1, u0ehi9]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [hlam, p1379_0]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p1379_1]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                rcases p1379_3 (m.d 0 5) (by simp) with h1400 | h1400
                · linarith only [h1400, hlam, hphi, ht0b, ht5b, p1379_1, u0elo4, u5ehi4]
                · linarith only [h1400, hc25, hlam, hphi, ht01, ht12, p1379_1, u0ehi9]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [h1373, hlam, hphi, p1379_1, u0ehi9, u0elo2]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [h1373, hlam, hphi, ht0b, ht5b, p1379_1, u0elo2, u5ehi1]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [h1373, hlam, hphi, ht0b, ht5b, p1379_1, u0elo2, u5ehi2]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [hlam, p1379_0]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [h1373, hlam, hphi, ht0b, ht5b, p1379_1, u0elo2, u5ehi4]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1379_1, u0ehi9]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                rcases p1379_3 (m.d 0 5) (by simp) with h1409 | h1409
                · linarith only [h1409, hlam, hphi, ht0b, ht5b, p1379_1, u0elo4, u5ehi1]
                · linarith only [h1409, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1379_1, u0ehi9]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                rcases p1379_3 (m.d 0 5) (by simp) with h1412 | h1412
                · linarith only [h1412, hlam, hphi, ht0b, ht5b, p1379_1, u0elo4, u5ehi2]
                · linarith only [h1412, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1379_1, u0ehi9]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [hc23, hc45, hlam, hphi, ht34, p0_1, p1379_1]
              · have p1379_0 := h1379c.1
                have p1379_1 := h1379c.2.1
                have p1379_2 := h1379c.2.2.1
                have p1379_3 := h1379c.2.2.2
                linarith only [hlam, p1379_0]
            · linarith only [h1378, hlam, p0_0]
          · rcases p0_3 (m.d 3 5) (by simp) with h1418 | h1418
            · rcases h5bigk with h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [hlam, p1419_0]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1419_1, u0elo4, u5ehi1]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1419_1, u0elo4, u5ehi2]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1419_1, u0elo4]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1419_1, u0elo4, u5ehi4]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p1419_1, u0ehi9]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [hlam, p1419_0]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                rcases p1419_3 (m.d 0 5) (by simp) with h1427 | h1427
                · linarith only [h1427, hlam, hphi, ht0b, ht5b, p1419_1, u0elo4, u5ehi2]
                · linarith only [h1427, hc15, hlam, hphi, ht01, p1419_1, u0ehi9]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p1419_1]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                rcases p1419_3 (m.d 0 5) (by simp) with h1431 | h1431
                · linarith only [h1431, hlam, hphi, ht0b, ht5b, p1419_1, u0elo4, u5ehi4]
                · linarith only [h1431, hc15, hlam, hphi, ht01, p1419_1, u0ehi9]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p1419_1, u0ehi9]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                rcases p1419_3 (m.d 0 5) (by simp) with h1435 | h1435
                · linarith only [h1435, hlam, hphi, ht0b, ht5b, p1419_1, u0elo4, u5ehi1]
                · linarith only [h1435, hc25, hlam, hphi, ht01, ht12, p1419_1, u0ehi9]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [hlam, p1419_0]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p1419_1]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                rcases p1419_3 (m.d 0 5) (by simp) with h1440 | h1440
                · linarith only [h1440, hlam, hphi, ht0b, ht5b, p1419_1, u0elo4, u5ehi4]
                · linarith only [h1440, hc25, hlam, hphi, ht01, ht12, p1419_1, u0ehi9]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [h1374, hc13, hlam, hphi, ht01, p1419_1, u0ehi9]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [h1373, hlam, hphi, ht0b, ht5b, p1419_1, u0elo2, u5ehi1]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [h1373, hlam, hphi, ht0b, ht5b, p1419_1, u0elo2, u5ehi2]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [hlam, p1419_0]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [h1373, hlam, hphi, ht0b, ht5b, p1419_1, u0elo2, u5ehi4]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1419_1, u0ehi9]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                rcases p1419_3 (m.d 0 5) (by simp) with h1449 | h1449
                · linarith only [h1449, hlam, hphi, ht0b, ht5b, p1419_1, u0elo4, u5ehi1]
                · linarith only [h1449, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1419_1, u0ehi9]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                rcases p1419_3 (m.d 0 5) (by simp) with h1452 | h1452
                · linarith only [h1452, hlam, hphi, ht0b, ht5b, p1419_1, u0elo4, u5ehi2]
                · linarith only [h1452, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1419_1, u0ehi9]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [hc23, hc45, hlam, hphi, ht34, p0_1, p1419_1]
              · have p1419_0 := h1419c.1
                have p1419_1 := h1419c.2.1
                have p1419_2 := h1419c.2.2.1
                have p1419_3 := h1419c.2.2.2
                linarith only [hlam, p1419_0]
            · linarith only [h1418, hlam, p0_0]
      · rcases p0_3 (m.d 2 3) (by simp) with h1458 | h1458
        · linarith only [h1458, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h1460 | h1460
          · rcases p0_3 (m.d 3 5) (by simp) with h1461 | h1461
            · rcases h5bigk with h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [hlam, p1462_0]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1462_1, u0elo4, u5ehi1]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1462_1, u0elo4, u5ehi2]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1462_1, u0elo4]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1462_1, u0elo4, u5ehi4]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p1462_1, u0ehi9]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [hlam, p1462_0]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                rcases p1462_3 (m.d 0 5) (by simp) with h1470 | h1470
                · linarith only [h1470, hlam, hphi, ht0b, ht5b, p1462_1, u0elo4, u5ehi2]
                · linarith only [h1470, hc15, hlam, hphi, ht01, p1462_1, u0ehi9]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p1462_1]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                rcases p1462_3 (m.d 0 5) (by simp) with h1474 | h1474
                · linarith only [h1474, hlam, hphi, ht0b, ht5b, p1462_1, u0elo4, u5ehi4]
                · linarith only [h1474, hc15, hlam, hphi, ht01, p1462_1, u0ehi9]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p1462_1, u0ehi9]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                rcases p1462_3 (m.d 0 5) (by simp) with h1478 | h1478
                · linarith only [h1478, hlam, hphi, ht0b, ht5b, p1462_1, u0elo4, u5ehi1]
                · linarith only [h1478, hc25, hlam, hphi, ht01, ht12, p1462_1, u0ehi9]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [hlam, p1462_0]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p1462_1]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                rcases p1462_3 (m.d 0 5) (by simp) with h1483 | h1483
                · linarith only [h1483, hlam, hphi, ht0b, ht5b, p1462_1, u0elo4, u5ehi4]
                · linarith only [h1483, hc25, hlam, hphi, ht01, ht12, p1462_1, u0ehi9]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [h1460, hc34, hlam, hphi, ht01, ht12, ht23, p1462_1, u0ehi9]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [h1373, hlam, hphi, ht0b, ht5b, p1462_1, u0elo2, u5ehi1]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [h1373, hlam, hphi, ht0b, ht5b, p1462_1, u0elo2, u5ehi2]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [hlam, p1462_0]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [h1373, hlam, hphi, ht0b, ht5b, p1462_1, u0elo2, u5ehi4]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1462_1, u0ehi9]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                rcases p1462_3 (m.d 0 5) (by simp) with h1492 | h1492
                · linarith only [h1492, hlam, hphi, ht0b, ht5b, p1462_1, u0elo4, u5ehi1]
                · linarith only [h1492, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1462_1, u0ehi9]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                rcases p1462_3 (m.d 0 5) (by simp) with h1495 | h1495
                · linarith only [h1495, hlam, hphi, ht0b, ht5b, p1462_1, u0elo4, u5ehi2]
                · linarith only [h1495, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1462_1, u0ehi9]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [hc23, hc45, hlam, hphi, ht34, p0_1, p1462_1]
              · have p1462_0 := h1462c.1
                have p1462_1 := h1462c.2.1
                have p1462_2 := h1462c.2.2.1
                have p1462_3 := h1462c.2.2.2
                linarith only [hlam, p1462_0]
            · linarith only [h1461, hlam, p0_0]
          · rcases p0_3 (m.d 3 5) (by simp) with h1501 | h1501
            · rcases h5bigk with h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [hlam, p1502_0]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1502_1, u0elo4, u5ehi1]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1502_1, u0elo4, u5ehi2]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1502_1, u0elo4]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1502_1, u0elo4, u5ehi4]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p1502_1, u0ehi9]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [hlam, p1502_0]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                rcases p1502_3 (m.d 0 5) (by simp) with h1510 | h1510
                · linarith only [h1510, hlam, hphi, ht0b, ht5b, p1502_1, u0elo4, u5ehi2]
                · linarith only [h1510, hc15, hlam, hphi, ht01, p1502_1, u0ehi9]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p1502_1]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                rcases p1502_3 (m.d 0 5) (by simp) with h1514 | h1514
                · linarith only [h1514, hlam, hphi, ht0b, ht5b, p1502_1, u0elo4, u5ehi4]
                · linarith only [h1514, hc15, hlam, hphi, ht01, p1502_1, u0ehi9]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p1502_1, u0ehi9]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                rcases p1502_3 (m.d 0 5) (by simp) with h1518 | h1518
                · linarith only [h1518, hlam, hphi, ht0b, ht5b, p1502_1, u0elo4, u5ehi1]
                · linarith only [h1518, hc25, hlam, hphi, ht01, ht12, p1502_1, u0ehi9]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [hlam, p1502_0]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p1502_1]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                rcases p1502_3 (m.d 0 5) (by simp) with h1523 | h1523
                · linarith only [h1523, hlam, hphi, ht0b, ht5b, p1502_1, u0elo4, u5ehi4]
                · linarith only [h1523, hc25, hlam, hphi, ht01, ht12, p1502_1, u0ehi9]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p1502_1, u0ehi9]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [h1373, hlam, hphi, ht0b, ht5b, p1502_1, u0elo2, u5ehi1]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [h1373, hlam, hphi, ht0b, ht5b, p1502_1, u0elo2, u5ehi2]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [hlam, p1502_0]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [h1373, hlam, hphi, ht0b, ht5b, p1502_1, u0elo2, u5ehi4]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1502_1, u0ehi9]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                rcases p1502_3 (m.d 0 5) (by simp) with h1532 | h1532
                · linarith only [h1532, hlam, hphi, ht0b, ht5b, p1502_1, u0elo4, u5ehi1]
                · linarith only [h1532, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1502_1, u0ehi9]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                rcases p1502_3 (m.d 0 5) (by simp) with h1535 | h1535
                · linarith only [h1535, hlam, hphi, ht0b, ht5b, p1502_1, u0elo4, u5ehi2]
                · linarith only [h1535, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1502_1, u0ehi9]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [hc23, hc45, hlam, hphi, ht34, p0_1, p1502_1]
              · have p1502_0 := h1502c.1
                have p1502_1 := h1502c.2.1
                have p1502_2 := h1502c.2.2.1
                have p1502_3 := h1502c.2.2.2
                linarith only [hlam, p1502_0]
            · linarith only [h1501, hlam, p0_0]
    · linarith only [h1373, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi7]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 3) (by simp) with h1542 | h1542
    · rcases p0_3 (m.d 1 3) (by simp) with h1543 | h1543
      · rcases p0_3 (m.d 2 3) (by simp) with h1544 | h1544
        · rcases p0_3 (m.d 3 4) (by simp) with h1545 | h1545
          · linarith only [h1545, hlam, p0_0]
          · rcases p0_3 (m.d 3 5) (by simp) with h1547 | h1547
            · rcases h5bigk with h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [hlam, p1548_0]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1548_1, u0elo4, u5ehi1]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1548_1, u0elo4, u5ehi2]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1548_1, u0elo4, u5ehi3]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1548_1, u0elo4, u5ehi4]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p1548_1, u0ehi9]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [hlam, p1548_0]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                rcases p1548_3 (m.d 0 5) (by simp) with h1556 | h1556
                · linarith only [h1556, hlam, hphi, ht0b, ht5b, p1548_1, u0elo4, u5ehi2]
                · linarith only [h1556, hc15, hlam, hphi, ht01, p1548_1, u0ehi9]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, p1548_1]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                rcases p1548_3 (m.d 0 5) (by simp) with h1560 | h1560
                · linarith only [h1560, hlam, hphi, ht0b, ht5b, p1548_1, u0elo4, u5ehi4]
                · linarith only [h1560, hc15, hlam, hphi, ht01, p1548_1, u0ehi9]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p1548_1, u0ehi9]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                rcases p1548_3 (m.d 0 5) (by simp) with h1564 | h1564
                · linarith only [h1564, hlam, hphi, ht0b, ht5b, p1548_1, u0elo4, u5ehi1]
                · linarith only [h1564, hc25, hlam, hphi, ht01, ht12, p1548_1, u0ehi9]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [hlam, p1548_0]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, p1548_1]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                rcases p1548_3 (m.d 0 5) (by simp) with h1569 | h1569
                · linarith only [h1569, hlam, hphi, ht0b, ht5b, p1548_1, u0elo4, u5ehi4]
                · linarith only [h1569, hc25, hlam, hphi, ht01, ht12, p1548_1, u0ehi9]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [h1543, hc13, hlam, hphi, ht01, p1548_1, u0ehi9]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [h1542, hlam, hphi, ht0b, ht5b, p1548_1, u0elo2, u5ehi1]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [h1542, hlam, hphi, ht0b, ht5b, p1548_1, u0elo2, u5ehi2]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [hlam, p1548_0]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [h1542, hlam, hphi, ht0b, ht5b, p1548_1, u0elo2, u5ehi4]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1548_1, u0ehi9]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                rcases p1548_3 (m.d 0 5) (by simp) with h1578 | h1578
                · linarith only [h1578, hlam, hphi, ht0b, ht5b, p1548_1, u0elo4, u5ehi1]
                · linarith only [h1578, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1548_1, u0ehi9]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                rcases p1548_3 (m.d 0 5) (by simp) with h1581 | h1581
                · linarith only [h1581, hlam, hphi, ht0b, ht5b, p1548_1, u0elo4, u5ehi2]
                · linarith only [h1581, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1548_1, u0ehi9]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [hc34, hc45, hlam, hphi, p0_1, p1548_1]
              · have p1548_0 := h1548c.1
                have p1548_1 := h1548c.2.1
                have p1548_2 := h1548c.2.2.1
                have p1548_3 := h1548c.2.2.2
                linarith only [hlam, p1548_0]
            · linarith only [h1547, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h1587 | h1587
          · linarith only [h1587, hlam, p0_0]
          · rcases p0_3 (m.d 3 5) (by simp) with h1589 | h1589
            · rcases h5bigk with h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [hlam, p1590_0]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1590_1, u0elo4, u5ehi1]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1590_1, u0elo4, u5ehi2]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [h1544, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1590_1, u0elo4]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1590_1, u0elo4, u5ehi4]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p1590_1, u0ehi9]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [hlam, p1590_0]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                rcases p1590_3 (m.d 0 5) (by simp) with h1598 | h1598
                · linarith only [h1598, hlam, hphi, ht0b, ht5b, p1590_1, u0elo4, u5ehi2]
                · linarith only [h1598, hc15, hlam, hphi, ht01, p1590_1, u0ehi9]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [h1544, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p1590_1]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                rcases p1590_3 (m.d 0 5) (by simp) with h1602 | h1602
                · linarith only [h1602, hlam, hphi, ht0b, ht5b, p1590_1, u0elo4, u5ehi4]
                · linarith only [h1602, hc15, hlam, hphi, ht01, p1590_1, u0ehi9]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p1590_1, u0ehi9]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                rcases p1590_3 (m.d 0 5) (by simp) with h1606 | h1606
                · linarith only [h1606, hlam, hphi, ht0b, ht5b, p1590_1, u0elo4, u5ehi1]
                · linarith only [h1606, hc25, hlam, hphi, ht01, ht12, p1590_1, u0ehi9]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [hlam, p1590_0]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [h1544, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p1590_1]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                rcases p1590_3 (m.d 0 5) (by simp) with h1611 | h1611
                · linarith only [h1611, hlam, hphi, ht0b, ht5b, p1590_1, u0elo4, u5ehi4]
                · linarith only [h1611, hc25, hlam, hphi, ht01, ht12, p1590_1, u0ehi9]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [h1543, hc13, hlam, hphi, ht01, p1590_1, u0ehi9]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [h1542, hlam, hphi, ht0b, ht5b, p1590_1, u0elo2, u5ehi1]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [h1542, hlam, hphi, ht0b, ht5b, p1590_1, u0elo2, u5ehi2]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [hlam, p1590_0]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [h1542, hlam, hphi, ht0b, ht5b, p1590_1, u0elo2, u5ehi4]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1590_1, u0ehi9]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                rcases p1590_3 (m.d 0 5) (by simp) with h1620 | h1620
                · linarith only [h1620, hlam, hphi, ht0b, ht5b, p1590_1, u0elo4, u5ehi1]
                · linarith only [h1620, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1590_1, u0ehi9]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                rcases p1590_3 (m.d 0 5) (by simp) with h1623 | h1623
                · linarith only [h1623, hlam, hphi, ht0b, ht5b, p1590_1, u0elo4, u5ehi2]
                · linarith only [h1623, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1590_1, u0ehi9]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [h1544, hc23, hc45, hlam, hphi, ht34, p0_1, p1590_1]
              · have p1590_0 := h1590c.1
                have p1590_1 := h1590c.2.1
                have p1590_2 := h1590c.2.2.1
                have p1590_3 := h1590c.2.2.2
                linarith only [hlam, p1590_0]
            · linarith only [h1589, hlam, p0_0]
      · rcases p0_3 (m.d 2 3) (by simp) with h1629 | h1629
        · rcases p0_3 (m.d 3 4) (by simp) with h1630 | h1630
          · linarith only [h1630, hlam, p0_0]
          · rcases p0_3 (m.d 3 5) (by simp) with h1632 | h1632
            · rcases h5bigk with h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [hlam, p1633_0]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1633_1, u0elo4, u5ehi1]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1633_1, u0elo4, u5ehi2]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [h1543, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1633_1, u0elo4]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1633_1, u0elo4, u5ehi4]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p1633_1, u0ehi9]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [hlam, p1633_0]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                rcases p1633_3 (m.d 0 5) (by simp) with h1641 | h1641
                · linarith only [h1641, hlam, hphi, ht0b, ht5b, p1633_1, u0elo4, u5ehi2]
                · linarith only [h1641, hc15, hlam, hphi, ht01, p1633_1, u0ehi9]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [h1543, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p1633_1]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                rcases p1633_3 (m.d 0 5) (by simp) with h1645 | h1645
                · linarith only [h1645, hlam, hphi, ht0b, ht5b, p1633_1, u0elo4, u5ehi4]
                · linarith only [h1645, hc15, hlam, hphi, ht01, p1633_1, u0ehi9]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p1633_1, u0ehi9]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                rcases p1633_3 (m.d 0 5) (by simp) with h1649 | h1649
                · linarith only [h1649, hlam, hphi, ht0b, ht5b, p1633_1, u0elo4, u5ehi1]
                · linarith only [h1649, hc25, hlam, hphi, ht01, ht12, p1633_1, u0ehi9]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [hlam, p1633_0]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [h1543, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p1633_1]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                rcases p1633_3 (m.d 0 5) (by simp) with h1654 | h1654
                · linarith only [h1654, hlam, hphi, ht0b, ht5b, p1633_1, u0elo4, u5ehi4]
                · linarith only [h1654, hc25, hlam, hphi, ht01, ht12, p1633_1, u0ehi9]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [h1629, hc23, hlam, hphi, ht01, ht12, p1633_1, u0ehi9]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [h1542, hlam, hphi, ht0b, ht5b, p1633_1, u0elo2, u5ehi1]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [h1542, hlam, hphi, ht0b, ht5b, p1633_1, u0elo2, u5ehi2]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [hlam, p1633_0]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [h1542, hlam, hphi, ht0b, ht5b, p1633_1, u0elo2, u5ehi4]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1633_1, u0ehi9]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                rcases p1633_3 (m.d 0 5) (by simp) with h1663 | h1663
                · linarith only [h1663, hlam, hphi, ht0b, ht5b, p1633_1, u0elo4, u5ehi1]
                · linarith only [h1663, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1633_1, u0ehi9]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                rcases p1633_3 (m.d 0 5) (by simp) with h1666 | h1666
                · linarith only [h1666, hlam, hphi, ht0b, ht5b, p1633_1, u0elo4, u5ehi2]
                · linarith only [h1666, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1633_1, u0ehi9]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [h1543, hc13, hc45, hlam, hphi, ht34, p0_1, p1633_1]
              · have p1633_0 := h1633c.1
                have p1633_1 := h1633c.2.1
                have p1633_2 := h1633c.2.2.1
                have p1633_3 := h1633c.2.2.2
                linarith only [hlam, p1633_0]
            · linarith only [h1632, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h1672 | h1672
          · linarith only [h1672, hlam, p0_0]
          · rcases p0_3 (m.d 3 5) (by simp) with h1674 | h1674
            · rcases h5bigk with h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [hlam, p1675_0]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1675_1, u0elo4, u5ehi1]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1675_1, u0elo4, u5ehi2]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [h1543, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1675_1, u0elo4]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [hlam, hphi, ht0b, ht5b, p1675_1, u0elo4, u5ehi4]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, p1675_1, u0ehi9]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [hlam, p1675_0]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                rcases p1675_3 (m.d 0 5) (by simp) with h1683 | h1683
                · linarith only [h1683, hlam, hphi, ht0b, ht5b, p1675_1, u0elo4, u5ehi2]
                · linarith only [h1683, hc15, hlam, hphi, ht01, p1675_1, u0ehi9]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [h1543, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, p1675_1]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                rcases p1675_3 (m.d 0 5) (by simp) with h1687 | h1687
                · linarith only [h1687, hlam, hphi, ht0b, ht5b, p1675_1, u0elo4, u5ehi4]
                · linarith only [h1687, hc15, hlam, hphi, ht01, p1675_1, u0ehi9]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht12, p1675_1, u0ehi9]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                rcases p1675_3 (m.d 0 5) (by simp) with h1691 | h1691
                · linarith only [h1691, hlam, hphi, ht0b, ht5b, p1675_1, u0elo4, u5ehi1]
                · linarith only [h1691, hc25, hlam, hphi, ht01, ht12, p1675_1, u0ehi9]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [hlam, p1675_0]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [h1543, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, p1675_1]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                rcases p1675_3 (m.d 0 5) (by simp) with h1696 | h1696
                · linarith only [h1696, hlam, hphi, ht0b, ht5b, p1675_1, u0elo4, u5ehi4]
                · linarith only [h1696, hc25, hlam, hphi, ht01, ht12, p1675_1, u0ehi9]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p1675_1, u0ehi9]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [h1542, hlam, hphi, ht0b, ht5b, p1675_1, u0elo2, u5ehi1]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [h1542, hlam, hphi, ht0b, ht5b, p1675_1, u0elo2, u5ehi2]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [hlam, p1675_0]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [h1542, hlam, hphi, ht0b, ht5b, p1675_1, u0elo2, u5ehi4]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1675_1, u0ehi9]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                rcases p1675_3 (m.d 0 5) (by simp) with h1705 | h1705
                · linarith only [h1705, hlam, hphi, ht0b, ht5b, p1675_1, u0elo4, u5ehi1]
                · linarith only [h1705, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1675_1, u0ehi9]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                rcases p1675_3 (m.d 0 5) (by simp) with h1708 | h1708
                · linarith only [h1708, hlam, hphi, ht0b, ht5b, p1675_1, u0elo4, u5ehi2]
                · linarith only [h1708, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1675_1, u0ehi9]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [h1543, hc13, hc45, hlam, hphi, ht34, p0_1, p1675_1]
              · have p1675_0 := h1675c.1
                have p1675_1 := h1675c.2.1
                have p1675_2 := h1675c.2.2.1
                have p1675_3 := h1675c.2.2.2
                linarith only [hlam, p1675_0]
            · linarith only [h1674, hlam, p0_0]
    · linarith only [h1542, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi7]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

end R2N4
