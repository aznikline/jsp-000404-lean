import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_13_25_L_R_L_R_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
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
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h13, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h10, h13, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                            · linarith only [h0, h16, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h10, h16, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h1, h10, h11, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                        · linarith only [h10, h20, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                            · linarith only [h10, h23, hc23, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                              · linarith only [h20, h25, h7, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h27 | h27
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                                  · rcases h5bigk with h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h20, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p29_1, u1ehi2]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h25, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p29_1, u3ehi2]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p29_1, u3ehi4]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      rcases p29_3 (m.d 0 5) (by simp) with h34 | h34
                                      · rcases p29_3 (m.d 1 5) (by simp) with h35 | h35
                                        · linarith only [h3, h35, hlam]
                                        · linarith only [h22, h35, hlam]
                                      · linarith only [h34, h6, hlam]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h3, hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h25, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p29_1, u3ehi2]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h20, hlam, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h1, h20, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h4, hlam, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h9, hlam, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h25, hlam, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h5, hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h1, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h1, h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h1, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h6, hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h22, hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h27, hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h28, hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [hlam, p29_0]
                                  · linarith only [h10, h28, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                · linarith only [h2, h22, h23, h27, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
                            · linarith only [h10, h61, hc23, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h63 | h63
                              · linarith only [h0, h63, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h65 | h65
                                · linarith only [h10, h22, h65, hc24, hlam, hphi, ht12, u1ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h67 | h67
                                  · linarith only [h10, h22, h67, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                  · linarith only [h10, h67, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
                      · linarith only [h7, h72, h8, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                        · linarith only [h72, h74, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                            · linarith only [h1, h5, h7, h74, h77, h8, hc01, hc24, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, u1ehi2, u3ehi3]
                            · linarith only [h7, h77, h8, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h7, h76, h8, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h0, h4, h7, h71, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h82 | h82
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h83 | h83
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h85 | h85
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h86 | h86
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h87 | h87
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h88 | h88
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h89 | h89
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h90 | h90
                                  · rcases h5bigk with h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h0, h4, h7, h82, h88, h89, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p91_1, u1ehi4, u3ehi4]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h0, h4, h88, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1, u3ehi4]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1, u3ehi4]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      rcases p91_3 (m.d 0 5) (by simp) with h96 | h96
                                      · rcases p91_3 (m.d 1 5) (by simp) with h97 | h97
                                        · linarith only [h3, h97, hlam]
                                        · linarith only [h86, h97, hlam]
                                      · linarith only [h6, h96, hlam]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h3, hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h86, h88, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p91_1, u3ehi4]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h7, h82, h86, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p91_1, u3ehi4]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h7, h82, h86, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p91_1]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h4, hlam, p91_1]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h83, hlam, p91_1]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h89, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p91_1, u3ehi4]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h7, h82, h89, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p91_1]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h5, hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h85, hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h88, hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h1, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p91_1]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h6, hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h86, hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h89, hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h90, hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [hlam, p91_0]
                                  · linarith only [h7, h82, h86, h90, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h7, h82, h86, h87, h89, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h7, h88, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                            · linarith only [h7, h82, h84, h86, h87, hc13, hlam, hphi, u1ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h126 | h126
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h127 | h127
                                · linarith only [h127, h82, h86, hc12, hlam, hphi, u1ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h129 | h129
                                  · linarith only [h129, h86, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                  · rcases h5bigk with h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h0, h125, h127, h4, h7, h83, h86, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p131_1, u1ehi3, u3ehi3]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h0, h125, h127, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p131_1, u3ehi3]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p131_1, u3ehi4]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h0, h125, h127, h4, h7, h83, h86, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p131_1, u1ehi3, u3ehi3]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h3, hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h125, h127, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p131_1, u3ehi3]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h2, h6, h7, h83, h86, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p131_1, u1ehi3, u3ehi4]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h86, hlam, p131_1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h4, hlam, p131_1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h83, hlam, p131_1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h2, h6, h86, hc01, hc25, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p131_1, u1ehi3, u3ehi4]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h127, hlam, p131_1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h5, hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h85, hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h126, hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h129, hlam, p131_1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h6, hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h2, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p131_1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h2, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p131_1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h2, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p131_1, u3ehi4]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [hlam, p131_0]
                              · linarith only [h126, h7, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                            · linarith only [h125, h7, h83, h86, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                        · linarith only [h1, h5, h84, h85, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h7, h82, h84, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h163 | h163
                          · linarith only [h163, h82, h83, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                            · linarith only [h0, h165, h4, h82, h83, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h161, h165, h7, h82, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h1, h161, h162, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h161, h7, h82, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h170 | h170
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h172 | h172
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h173 | h173
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h174 | h174
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h175 | h175
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h176 | h176
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h177 | h177
                                  · rcases h5bigk with h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [hlam, p178_0]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p178_1, u1ehi4]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h0, h175, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p178_1, u3ehi4]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p178_1, u3ehi4]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      rcases p178_3 (m.d 0 5) (by simp) with h183 | h183
                                      · rcases p178_3 (m.d 1 5) (by simp) with h184 | h184
                                        · linarith only [h184, h3, hlam]
                                        · linarith only [h173, h184, hlam]
                                      · linarith only [h183, h6, hlam]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h3, hlam, p178_0]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [hlam, p178_0]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h175, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p178_1, u3ehi4]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h170, h174, h82, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p178_1, u3ehi4]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h170, h174, h82, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p178_1]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h4, hlam, p178_1]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h170, hlam, p178_1]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [hlam, p178_0]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h170, h174, h82, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p178_1, u3ehi4]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h170, h174, h82, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p178_1]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h5, hlam, p178_0]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h172, hlam, p178_0]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h175, hlam, p178_0]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [hlam, p178_0]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h1, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p178_1]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h6, hlam, p178_0]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h173, hlam, p178_0]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h176, hlam, p178_0]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [h177, hlam, p178_0]
                                    · have p178_0 := h178c.1
                                      have p178_1 := h178c.2.1
                                      have p178_2 := h178c.2.2.1
                                      have p178_3 := h178c.2.2.2
                                      linarith only [hlam, p178_0]
                                  · linarith only [h1, h171, h173, h177, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h1, h171, h173, h176, h82, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                              · linarith only [h1, h170, h175, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                            · linarith only [h170, h174, h7, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                          · linarith only [h170, h173, h82, hlam]
                        · linarith only [h171, h172, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h214 | h214
                        · linarith only [h171, h214, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h170, h214, h7, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h217 | h217
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h218 | h218
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h219 | h219
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h220 | h220
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h221 | h221
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h222 | h222
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h223 | h223
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
                                      linarith only [h0, h170, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p224_1, u1ehi1]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h0, h170, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p224_1, u1ehi1]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p224_1, u3ehi4]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      rcases p224_3 (m.d 0 5) (by simp) with h229 | h229
                                      · rcases p224_3 (m.d 1 5) (by simp) with h230 | h230
                                        · linarith only [h230, h3, hlam]
                                        · linarith only [h219, h230, hlam]
                                      · linarith only [h229, h6, hlam]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h3, hlam, p224_0]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [hlam, p224_0]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h170, hlam, p224_0]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h219, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p224_1, u3ehi4]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h0, h170, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p224_1]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h4, hlam, p224_1]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h0, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p224_1]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [hlam, p224_0]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p224_1, u3ehi4]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h0, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p224_1]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h5, hlam, p224_0]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h218, hlam, p224_0]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h221, hlam, p224_0]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [hlam, p224_0]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h1, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p224_1]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h6, hlam, p224_0]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h219, hlam, p224_0]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h222, hlam, p224_0]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [h223, hlam, p224_0]
                                    · have p224_0 := h224c.1
                                      have p224_1 := h224c.2.1
                                      have p224_2 := h224c.2.2.1
                                      have p224_3 := h224c.2.2.2
                                      linarith only [hlam, p224_0]
                                  · linarith only [h1, h217, h219, h223, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h219, h222, h82, hlam]
                              · linarith only [h218, h221, h7, hlam]
                            · linarith only [h218, h220, h7, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h258 | h258
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h259 | h259
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h260 | h260
                                · linarith only [h219, h260, h82, hc24, hlam, hphi, ht12, u1ehi1]
                                · linarith only [h2, h260, h6, h82, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                              · linarith only [h1, h218, h259, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h2, h217, h219, h258, h6, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h217, h218, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h266 | h266
                        · linarith only [h217, h266, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h268 | h268
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h269 | h269
                            · linarith only [h217, h269, hc23, hlam, hphi, ht12, u1ehi2]
                            · linarith only [h269, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h272 | h272
                            · linarith only [h217, h272, h7, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h272, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h275 | h275
                · rcases m.htr 1 2 4 (by decide) (by decide) with h276 | h276
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h277 | h277
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h278 | h278
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h279 | h279
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h280 | h280
                          · linarith only [h2, h280, h6, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h282 | h282
                            · linarith only [h0, h275, h282, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1, h278, h282, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h1, h278, h279, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h286 | h286
                        · linarith only [h278, h286, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h288 | h288
                          · linarith only [h2, h288, h6, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h290 | h290
                            · linarith only [h0, h275, h290, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h292 | h292
                              · linarith only [h275, h278, h292, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h294 | h294
                                · linarith only [h2, h276, h294, h6, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h296 | h296
                                  · linarith only [h2, h278, h296, h6, hc34, hlam, hphi, u3ehi1]
                                  · linarith only [h278, h296, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · linarith only [h0, h275, h277, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h2, h275, h276, h6, hc45, hlam, hphi, ht34, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h301 | h301
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h302 | h302
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h303 | h303
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h304 | h304
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h305 | h305
                          · linarith only [h2, h305, h6, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h307 | h307
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h308 | h308
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h309 | h309
                                · linarith only [h2, h309, h6, hc24, hlam, hphi, ht12, u1ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h311 | h311
                                  · linarith only [h2, h311, h6, hc34, hlam, hphi, ht12, ht23, u1ehi3]
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
                                      linarith only [h275, h302, h305, h307, h309, hc05, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p313_1, u1ehi3, u3ehi3]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [h0, h307, h309, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p313_1, u3ehi3]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p313_1, u3ehi4]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [h6, hlam, p313_1]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [h3, hlam, p313_0]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [hlam, p313_0]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [h307, h309, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p313_1, u3ehi3]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [h275, h302, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p313_1, u3ehi4]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [h305, hlam, p313_1]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [h4, hlam, p313_1]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [h302, hlam, p313_1]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [hlam, p313_0]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p313_1, u3ehi4]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [h309, hlam, p313_1]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [h5, hlam, p313_0]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [h304, hlam, p313_0]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [h308, hlam, p313_0]
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
                                      linarith only [h3, hc45, hlam, hphi, ht12, ht23, ht34, p313_1, u1ehi4]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [h275, h301, h307, hc23, hc45, hlam, hphi, ht12, ht34, p313_1, u1ehi4, u3ehi3]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [h308, hc45, hlam, hphi, ht34, p313_1, u3ehi4]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht34, p313_1, u3ehi4]
                                    · have p313_0 := h313c.1
                                      have p313_1 := h313c.2.1
                                      have p313_2 := h313c.2.2.1
                                      have p313_3 := h313c.2.2.2
                                      linarith only [hlam, p313_0]
                              · linarith only [h275, h308, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                            · linarith only [h275, h302, h303, h305, h307, hc13, hlam, hphi, u1ehi3]
                        · linarith only [h303, h304, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h275, h301, h303, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h343 | h343
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h344 | h344
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h345 | h345
                          · linarith only [h2, h345, h6, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h347 | h347
                            · linarith only [h301, h302, h347, h4, h6, hc45, hlam, hphi, ht34, u3ehi3]
                            · linarith only [h275, h347, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                        · linarith only [h1, h343, h344, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h275, h301, h343, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h352 | h352
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h353 | h353
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h354 | h354
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h355 | h355
                          · linarith only [h2, h355, h6, hlam]
                          · linarith only [h301, h352, h355, hlam]
                        · linarith only [h353, h354, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h359 | h359
                        · linarith only [h2, h353, h359, h6, hc45, hlam, hphi, ht34, u3ehi4]
                        · linarith only [h275, h352, h359, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h362 | h362
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h363 | h363
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h364 | h364
                          · linarith only [h2, h364, h6, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h366 | h366
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h367 | h367
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h368 | h368
                                · linarith only [h2, h366, h368, h6, hc23, hlam, hphi, ht12, u1ehi3]
                                · linarith only [h301, h368, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                              · linarith only [h1, h363, h367, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h275, h366, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                        · linarith only [h362, h363, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
                        · linarith only [h2, h362, h374, h6, hc45, hlam, hphi, ht34, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h376 | h376
                          · linarith only [h2, h376, h6, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h378 | h378
                            · linarith only [h362, h378, hc23, hlam, hphi, ht12, u1ehi2]
                            · linarith only [h275, h378, hc34, hlam, hphi, ht12, ht23, u1ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h381 | h381
              · rcases m.htr 1 2 3 (by decide) (by decide) with h382 | h382
                · rcases m.htr 1 2 4 (by decide) (by decide) with h383 | h383
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h384 | h384
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h385 | h385
                      · linarith only [h1, h385, h5, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h387 | h387
                        · linarith only [h1, h387, h5, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h389 | h389
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h390 | h390
                            · linarith only [h385, h390, hc23, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h392 | h392
                              · linarith only [h382, h385, h392, h5, hc34, hlam, hphi, u3ehi0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h394 | h394
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h395 | h395
                                  · rcases h5bigk with h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [hlam, p396_0]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h381, h387, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p396_1, u3ehi1]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h2, h381, h392, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p396_1, u3ehi2]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h5, hlam, p396_1]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      rcases p396_3 (m.d 0 5) (by simp) with h401 | h401
                                      · rcases p396_3 (m.d 1 5) (by simp) with h402 | h402
                                        · linarith only [h3, h402, hlam]
                                        · linarith only [h389, h402, hlam]
                                      · linarith only [h381, h401, hlam]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h3, hlam, p396_0]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [hlam, p396_0]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h389, h392, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p396_1, u3ehi2]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h387, hlam, p396_1]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h0, h383, h389, hc01, hc45, hlam, hphi, ht0b, ht5b, p396_1]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h4, hlam, p396_1]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h384, hlam, p396_1]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [hlam, p396_0]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h392, hlam, p396_1]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p396_1]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h3, h395, hc34, hlam, hphi, ht12, ht23, p396_1, u1ehi4]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h395, hc34, hlam, hphi, ht12, ht23, p396_1, u1ehi4]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h392, h395, hc34, hlam, hphi, p396_1, u3ehi2]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [hlam, p396_0]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      rcases p396_3 (m.d 0 5) (by simp) with h420 | h420
                                      · linarith only [h420, h5, hlam]
                                      · linarith only [h381, h420, hlam]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h381, hlam, p396_0]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h389, hlam, p396_0]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h394, hlam, p396_0]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [h395, hlam, p396_0]
                                    · have p396_0 := h396c.1
                                      have p396_1 := h396c.2.1
                                      have p396_2 := h396c.2.2.1
                                      have p396_3 := h396c.2.2.2
                                      linarith only [hlam, p396_0]
                                  · linarith only [h385, h395, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                · linarith only [h0, h383, h389, h390, h394, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h430 | h430
                            · linarith only [h385, h430, hc23, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h432 | h432
                              · linarith only [h382, h385, h432, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h434 | h434
                                · linarith only [h383, h389, h434, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h436 | h436
                                  · linarith only [h385, h389, h436, hc34, hlam, hphi, u3ehi1]
                                  · linarith only [h385, h436, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · linarith only [h0, h382, h384, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h440 | h440
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h441 | h441
                      · linarith only [h1, h441, h5, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h443 | h443
                        · linarith only [h1, h443, h5, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h445 | h445
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h446 | h446
                            · linarith only [h382, h441, h446, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · linarith only [h382, h383, h446, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h2, h381, h382, h383, h445, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h382, h4, h440, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h451 | h451
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h452 | h452
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h453 | h453
                      · linarith only [h1, h453, h5, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h382, h451, h453, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h456 | h456
                      · linarith only [h1, h456, h5, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h382, h451, h456, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h459 | h459
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h460 | h460
                      · linarith only [h1, h460, h5, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h462 | h462
                        · linarith only [h1, h462, h5, hlam]
                        · linarith only [h382, h459, h462, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h465 | h465
                      · linarith only [h1, h465, h5, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h467 | h467
                        · linarith only [h1, h467, h5, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h469 | h469
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h470 | h470
                            · linarith only [h465, h470, hc23, hlam, hphi, ht12, u1ehi2]
                            · linarith only [h382, h470, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h473 | h473
                            · linarith only [h382, h465, h473, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h382, h473, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h476 | h476
                · rcases m.htr 1 2 4 (by decide) (by decide) with h477 | h477
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h478 | h478
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h479 | h479
                      · linarith only [h1, h479, h5, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h481 | h481
                        · linarith only [h2, h381, h479, h481, h5, hc45, hlam, hphi, ht34, u3ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h483 | h483
                          · linarith only [h2, h381, h483, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h485 | h485
                            · linarith only [h476, h479, h485, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h487 | h487
                              · linarith only [h476, h479, h487, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h489 | h489
                                · linarith only [h0, h381, h477, h489, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h491 | h491
                                  · linarith only [h2, h381, h479, h491, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                  · linarith only [h479, h491, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · linarith only [h0, h4, h476, h478, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h2, h381, h476, h477, hc45, hlam, hphi, ht34, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h496 | h496
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h497 | h497
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h498 | h498
                      · linarith only [h1, h498, h5, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h476, h496, h498, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h501 | h501
                      · linarith only [h1, h5, h501, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h476, h496, h501, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h504 | h504
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h505 | h505
                      · linarith only [h1, h5, h505, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h507 | h507
                        · linarith only [h2, h381, h5, h505, h507, hc45, hlam, hphi, ht34, u3ehi0]
                        · linarith only [h476, h504, h507, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h510 | h510
                      · linarith only [h1, h5, h510, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h512 | h512
                        · linarith only [h2, h381, h5, h510, h512, hc45, hlam, hphi, ht34, u3ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h514 | h514
                          · linarith only [h2, h381, h514, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h516 | h516
                            · linarith only [h510, h516, hc23, hlam, hphi, ht12, u1ehi2]
                            · linarith only [h476, h516, hc34, hlam, hphi, ht12, ht23, u1ehi1]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h519 | h519
            · rcases m.htr 0 4 5 (by decide) (by decide) with h520 | h520
              · rcases m.htr 1 2 3 (by decide) (by decide) with h521 | h521
                · rcases m.htr 1 2 4 (by decide) (by decide) with h522 | h522
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h523 | h523
                    · linarith only [h0, h4, h523, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h525 | h525
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h526 | h526
                        · linarith only [h521, h523, h526, hlam]
                        · linarith only [h525, h526, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h529 | h529
                        · linarith only [h525, h529, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h531 | h531
                          · linarith only [h522, h523, h531, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h533 | h533
                            · linarith only [h0, h4, h521, h525, h533, hc25, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h535 | h535
                              · linarith only [h0, h4, h522, h529, h533, h535, hc25, hlam, hphi, ht12, u1ehi2]
                              · linarith only [h0, h4, h522, h533, h535, hc35, hlam, hphi, u3ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h538 | h538
                    · linarith only [h0, h4, h538, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h540 | h540
                      · linarith only [h521, h522, h540, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h542 | h542
                        · linarith only [h540, h542, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h544 | h544
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h545 | h545
                            · linarith only [h0, h1, h4, h519, h521, h542, h545, hc01, hc25, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, u1ehi2, u3ehi3]
                            · linarith only [h521, h522, h545, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h2, h520, h521, h522, h544, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h549 | h549
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h550 | h550
                    · linarith only [h4, h521, h550, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h552 | h552
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h553 | h553
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h554 | h554
                          · linarith only [h549, h550, h554, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h556 | h556
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h557 | h557
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h558 | h558
                                · linarith only [h0, h4, h549, h554, h557, h558, hc23, hlam, hphi, ht12, u1ehi3]
                                · linarith only [h0, h4, h549, h556, h558, hc45, hlam, hphi, ht34, u3ehi3]
                              · linarith only [h1, h553, h557, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h521, h556, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                        · linarith only [h1, h519, h552, h553, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h521, h549, h552, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h565 | h565
                    · linarith only [h4, h521, h565, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h567 | h567
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h568 | h568
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h569 | h569
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h570 | h570
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h571 | h571
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h572 | h572
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h573 | h573
                                  · rcases h5bigk with h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p574_1, u1ehi4]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h4, hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p574_1, u3ehi4]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      rcases p574_3 (m.d 0 5) (by simp) with h579 | h579
                                      · rcases p574_3 (m.d 1 5) (by simp) with h580 | h580
                                        · linarith only [h3, h580, hlam]
                                        · linarith only [h569, h580, hlam]
                                      · linarith only [h520, h579, hlam]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h3, hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h565, hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p574_1, u3ehi4]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h1, h567, h569, hc01, hc45, hlam, hphi, ht0b, ht5b, p574_1]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h3, h570, h572, hc23, hlam, hphi, ht12, p574_1, u1ehi4]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h570, h572, hc23, hlam, hphi, ht12, p574_1, u1ehi4]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h570, h572, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p574_1, u3ehi4]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      rcases p574_3 (m.d 0 5) (by simp) with h593 | h593
                                      · linarith only [h4, h593, hlam]
                                      · linarith only [h520, h593, hlam]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h519, hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h568, hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h571, hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h1, h519, hc01, hc45, hlam, hphi, ht0b, ht5b, p574_1]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h520, hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h569, hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h572, hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h573, hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [hlam, p574_0]
                                  · linarith only [h1, h567, h569, h573, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h1, h549, h567, h569, h572, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                              · linarith only [h521, h568, h571, hc15, hlam, hphi, u1ehi1]
                            · linarith only [h521, h568, h570, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h610 | h610
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h611 | h611
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h612 | h612
                                · linarith only [h549, h569, h612, hc24, hlam, hphi, ht12, u1ehi1]
                                · linarith only [h2, h520, h549, h612, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                              · linarith only [h1, h568, h611, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h521, h567, h610, hc14, hlam, hphi, u1ehi1]
                        · linarith only [h567, h568, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h618 | h618
                        · linarith only [h567, h618, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h620 | h620
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h621 | h621
                            · linarith only [h567, h621, hc23, hlam, hphi, ht12, u1ehi2]
                            · linarith only [h521, h621, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h624 | h624
                            · linarith only [h521, h567, h624, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h521, h624, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h627 | h627
                · rcases m.htr 1 2 4 (by decide) (by decide) with h628 | h628
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h629 | h629
                    · linarith only [h0, h4, h629, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h631 | h631
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h632 | h632
                        · linarith only [h627, h629, h632, hlam]
                        · linarith only [h631, h632, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h635 | h635
                        · linarith only [h2, h520, h631, h635, hc45, hlam, hphi, ht34, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h637 | h637
                          · linarith only [h2, h520, h637, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h639 | h639
                            · linarith only [h631, h639, hc23, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h641 | h641
                              · linarith only [h0, h628, h635, h639, h641, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                              · linarith only [h0, h1, h4, h519, h628, h639, h641, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h2, h520, h627, h628, hc45, hlam, hphi, ht34, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h645 | h645
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h646 | h646
                    · linarith only [h3, h4, h627, h646, hc23, hlam, hphi, ht12, u1ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h648 | h648
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h649 | h649
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h650 | h650
                          · linarith only [h2, h520, h650, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h652 | h652
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h653 | h653
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h654 | h654
                                · linarith only [h0, h4, h520, h645, h653, h654, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h4, h645, h652, h654, hc45, hlam, hphi, ht34, u3ehi3]
                              · linarith only [h1, h649, h653, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h627, h652, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                        · linarith only [h1, h519, h648, h649, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h627, h645, h648, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h661 | h661
                    · linarith only [h4, h627, h661, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h663 | h663
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h664 | h664
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h665 | h665
                          · linarith only [h2, h520, h665, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h667 | h667
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h668 | h668
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h669 | h669
                                · linarith only [h2, h520, h645, h667, h669, hc23, hlam, hphi, ht12, u1ehi1]
                                · linarith only [h645, h669, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                              · linarith only [h1, h664, h668, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h627, h664, h667, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h663, h664, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h675 | h675
                        · linarith only [h2, h520, h663, h675, hc45, hlam, hphi, ht34, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h677 | h677
                          · linarith only [h2, h520, h677, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h679 | h679
                            · linarith only [h627, h663, h679, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h627, h679, hc34, hlam, hphi, ht12, ht23, u1ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h682 | h682
              · rcases m.htr 1 2 3 (by decide) (by decide) with h683 | h683
                · rcases m.htr 1 2 4 (by decide) (by decide) with h684 | h684
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h685 | h685
                    · linarith only [h0, h4, h685, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h687 | h687
                      · linarith only [h1, h519, h687, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h689 | h689
                        · linarith only [h1, h519, h689, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h691 | h691
                          · linarith only [h684, h685, h691, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h693 | h693
                            · linarith only [h0, h4, h683, h687, h693, hc25, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h695 | h695
                              · linarith only [h0, h2, h4, h519, h682, h684, h687, h691, h693, h695, hc01, hc25, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, u1ehi2, u3ehi0]
                              · linarith only [h0, h4, h684, h693, h695, hc35, hlam, hphi, u3ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h698 | h698
                    · linarith only [h0, h4, h698, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h700 | h700
                      · linarith only [h1, h519, h700, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h702 | h702
                        · linarith only [h1, h519, h702, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h704 | h704
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h705 | h705
                            · linarith only [h0, h4, h683, h700, h704, h705, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h683, h684, h705, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h683, h684, h704, hc45, hlam, hphi, ht34, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h709 | h709
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h710 | h710
                    · linarith only [h1, h4, h519, h683, h710, hc02, hc35, hlam, hphi, ht23]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h712 | h712
                      · linarith only [h1, h519, h712, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h683, h709, h712, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h715 | h715
                    · linarith only [h1, h3, h4, h519, h683, h715, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h717 | h717
                      · linarith only [h1, h519, h717, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h719 | h719
                        · linarith only [h1, h519, h719, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h721 | h721
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h722 | h722
                            · linarith only [h683, h717, h722, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h683, h722, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h725 | h725
                            · linarith only [h683, h717, h725, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h683, h725, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h728 | h728
                · rcases m.htr 1 2 4 (by decide) (by decide) with h729 | h729
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h730 | h730
                    · linarith only [h0, h4, h730, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h732 | h732
                      · linarith only [h1, h519, h732, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h734 | h734
                        · linarith only [h2, h519, h682, h732, h734, hc45, hlam, hphi, ht34, u3ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h736 | h736
                          · linarith only [h2, h682, h736, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h738 | h738
                            · linarith only [h0, h4, h728, h732, h738, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h740 | h740
                              · linarith only [h0, h4, h729, h738, h740, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                              · linarith only [h0, h4, h729, h738, h740, hc35, hlam, hphi, u3ehi2]
                  · linarith only [h2, h682, h728, h729, hc45, hlam, hphi, ht34, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h744 | h744
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h745 | h745
                    · linarith only [h0, h4, h745, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h747 | h747
                      · linarith only [h1, h519, h747, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h728, h744, h747, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h750 | h750
                    · linarith only [h0, h4, h750, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h752 | h752
                      · linarith only [h1, h519, h752, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h754 | h754
                        · linarith only [h2, h519, h682, h752, h754, hc45, hlam, hphi, ht34, u3ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h756 | h756
                          · linarith only [h2, h682, h756, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h758 | h758
                            · linarith only [h728, h752, h758, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h728, h758, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h764 | h764
    · linarith only [h0, h764, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h766 | h766
      · linarith only [h0, h766, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h768 | h768
        · linarith only [h0, h768, hc12, hlam, hphi, u1ehi4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h770 | h770
          · rcases m.htr 0 3 5 (by decide) (by decide) with h771 | h771
            · rcases m.htr 0 4 5 (by decide) (by decide) with h772 | h772
              · rcases m.htr 1 2 3 (by decide) (by decide) with h773 | h773
                · rcases m.htr 1 2 4 (by decide) (by decide) with h774 | h774
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h775 | h775
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h776 | h776
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h777 | h777
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h778 | h778
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h779 | h779
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h780 | h780
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h781 | h781
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h782 | h782
                                  · rcases h5bigk with h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c | h783c
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [hlam, p783_0]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [h768, hlam, p783_1]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [h770, h780, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p783_1, u3ehi4]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [h766, h772, h773, h776, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p783_1, u3ehi4]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      rcases p783_3 (m.d 0 5) (by simp) with h788 | h788
                                      · rcases p783_3 (m.d 1 5) (by simp) with h789 | h789
                                        · rcases p783_3 (m.d 2 5) (by simp) with h790 | h790
                                          · linarith only [h770, h790, hlam]
                                          · linarith only [h781, h790, hlam]
                                        · linarith only [h778, h789, hlam]
                                      · linarith only [h772, h788, hlam]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [h768, h773, h776, h778, hc12, hlam, hphi, p783_1, u1ehi0]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [hlam, p783_0]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [h773, h776, h778, h780, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p783_1, u3ehi4]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [h773, h776, h778, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p783_1, u3ehi4]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      rcases p783_3 (m.d 0 5) (by simp) with h799 | h799
                                      · linarith only [h768, h799, hlam]
                                      · linarith only [h772, h799, hlam]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [h770, hlam, p783_1]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [h775, hlam, p783_1]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [hlam, p783_0]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p783_1, u3ehi4]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [h0, h770, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p783_1]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [h771, hlam, p783_0]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [h777, hlam, p783_0]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [h780, hlam, p783_0]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [hlam, p783_0]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [h764, h771, h773, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p783_1]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [h772, hlam, p783_0]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [h778, hlam, p783_0]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [h781, hlam, p783_0]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [h782, hlam, p783_0]
                                    · have p783_0 := h783c.1
                                      have p783_1 := h783c.2.1
                                      have p783_2 := h783c.2.2.1
                                      have p783_3 := h783c.2.2.2
                                      linarith only [hlam, p783_0]
                                  · linarith only [h773, h779, h781, h782, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h818 | h818
                                  · linarith only [h773, h779, h780, h781, h818, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                                  · rcases h5bigk with h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [hlam, p820_0]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h768, hlam, p820_1]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h779, h781, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p820_1, u3ehi3]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h768, h773, h776, h778, h818, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p820_1, u3ehi3]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h768, h773, h776, h778, h779, h781, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p820_1, u3ehi3]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h768, h773, h776, h778, hc12, hlam, hphi, p820_1, u1ehi0]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [hlam, p820_0]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h773, h776, h778, h779, h781, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p820_1, u3ehi3]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h773, h776, h778, h818, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p820_1, u3ehi3]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h773, h776, h778, h779, h781, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p820_1, u3ehi3]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h770, hlam, p820_1]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h775, hlam, p820_1]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [hlam, p820_0]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h818, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p820_1, u3ehi3]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h781, hlam, p820_1]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h771, hlam, p820_0]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h777, hlam, p820_0]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h780, hlam, p820_0]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [hlam, p820_0]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h818, hlam, p820_1]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h772, hlam, p820_0]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h778, hlam, p820_0]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h766, h772, h773, h776, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p820_1]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [h766, h772, h773, h776, h818, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p820_1, u3ehi3]
                                    · have p820_0 := h820c.1
                                      have p820_1 := h820c.2.1
                                      have p820_2 := h820c.2.2.1
                                      have p820_3 := h820c.2.2.2
                                      linarith only [hlam, p820_0]
                              · linarith only [h779, h780, hc35, hlam, hphi, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h847 | h847
                              · linarith only [h779, h847, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h849 | h849
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h850 | h850
                                  · rcases h5bigk with h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [hlam, p851_0]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h768, hlam, p851_1]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h847, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p851_1, u3ehi2]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h768, h773, h776, h778, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p851_1, u3ehi4]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      rcases p851_3 (m.d 0 5) (by simp) with h856 | h856
                                      · rcases p851_3 (m.d 1 5) (by simp) with h857 | h857
                                        · rcases p851_3 (m.d 2 5) (by simp) with h858 | h858
                                          · linarith only [h770, h858, hlam]
                                          · linarith only [h849, h858, hlam]
                                        · linarith only [h778, h857, hlam]
                                      · linarith only [h772, h856, hlam]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h768, h773, h776, h778, hc12, hlam, hphi, p851_1, u1ehi0]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [hlam, p851_0]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h773, h776, h778, h847, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p851_1, u3ehi2]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h773, h776, h778, h847, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p851_1, u3ehi2]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      rcases p851_3 (m.d 0 5) (by simp) with h867 | h867
                                      · linarith only [h768, h867, hlam]
                                      · linarith only [h772, h867, hlam]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h770, hlam, p851_1]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h775, hlam, p851_1]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [hlam, p851_0]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h847, hlam, p851_1]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h0, h770, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p851_1]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h771, hlam, p851_0]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h777, hlam, p851_0]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h764, h771, h773, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p851_1]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [hlam, p851_0]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h764, h771, h773, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p851_1]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h772, hlam, p851_0]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h778, hlam, p851_0]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h849, hlam, p851_0]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [h850, hlam, p851_0]
                                    · have p851_0 := h851c.1
                                      have p851_1 := h851c.2.1
                                      have p851_2 := h851c.2.2.1
                                      have p851_3 := h851c.2.2.2
                                      linarith only [hlam, p851_0]
                                  · linarith only [h766, h772, h773, h776, h779, h850, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h886 | h886
                                  · linarith only [h773, h776, h779, h849, h886, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                                  · linarith only [h779, h886, hc45, hlam, hphi, ht34, u3ehi2]
                          · linarith only [h766, h772, h778, hlam]
                        · linarith only [h764, h771, h777, hlam]
                      · linarith only [h764, h771, h776, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h0, h775, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h774, hc24, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h773, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h895 | h895
                · rcases m.htr 1 2 4 (by decide) (by decide) with h896 | h896
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h897 | h897
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h898 | h898
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h899 | h899
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h900 | h900
                          · linarith only [h766, h772, h895, h898, h900, hc12, hlam, hphi, u1ehi0]
                          · linarith only [h766, h900, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                        · linarith only [h771, h898, h899, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h764, h898, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h770, h895, h897, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h764, h895, h896, hc24, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h895, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h908 | h908
              · rcases m.htr 1 2 3 (by decide) (by decide) with h909 | h909
                · rcases m.htr 1 2 4 (by decide) (by decide) with h910 | h910
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h911 | h911
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h912 | h912
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h913 | h913
                        · linarith only [h764, h771, h909, h913, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h912, h913, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h764, h912, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h770, h909, h911, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h764, h909, h910, hc24, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h909, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h920 | h920
                · rcases m.htr 1 2 4 (by decide) (by decide) with h921 | h921
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h922 | h922
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h923 | h923
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h924 | h924
                        · linarith only [h764, h771, h920, h924, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h923, h924, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h764, h923, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h770, h920, h922, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h764, h920, h921, hc24, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h920, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h931 | h931
            · rcases m.htr 0 4 5 (by decide) (by decide) with h932 | h932
              · rcases m.htr 1 2 3 (by decide) (by decide) with h933 | h933
                · rcases m.htr 1 2 4 (by decide) (by decide) with h934 | h934
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h935 | h935
                    · linarith only [h0, h770, h935, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h935, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h764, h933, h934, hc24, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h933, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h940 | h940
                · rcases m.htr 1 2 4 (by decide) (by decide) with h941 | h941
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h942 | h942
                    · linarith only [h0, h770, h942, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h942, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h764, h940, h941, hc24, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h940, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h947 | h947
              · rcases m.htr 1 2 3 (by decide) (by decide) with h948 | h948
                · rcases m.htr 1 2 4 (by decide) (by decide) with h949 | h949
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h950 | h950
                    · linarith only [h0, h770, h950, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h950, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h764, h948, h949, hc24, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h948, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h955 | h955
                · rcases m.htr 1 2 4 (by decide) (by decide) with h956 | h956
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h957 | h957
                    · linarith only [h0, h770, h957, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h957, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h764, h955, h956, hc24, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h955, hc23, hlam, hphi, ht12, u1ehi0]

end R2N4
