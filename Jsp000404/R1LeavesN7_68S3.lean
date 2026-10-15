import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                          · linarith only [h0, h10, h13, h5, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                            · linarith only [h0, h10, h15, h5, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h10, h12, h15, h5, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
                          · linarith only [h0, h10, h12, h18, h5, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                            · linarith only [h0, h10, h12, h20, h5, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                              · linarith only [h12, h18, h22, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                                · linarith only [h0, h10, h22, h24, h3, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
                                  · linarith only [h0, h10, h20, h24, h26, h3, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · rcases h2bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      rcases p28_3 (m.d 0 2) (by simp) with h30 | h30
                                      · rcases p28_3 (m.d 1 2) (by simp) with h31 | h31
                                        · linarith only [h0, h31, hlam]
                                        · rcases p28_3 (m.d 2 3) (by simp) with h33 | h33
                                          · linarith only [h3, h33, hlam]
                                          · rcases p28_3 (m.d 2 4) (by simp) with h35 | h35
                                            · linarith only [h35, h4, hlam]
                                            · rcases p28_3 (m.d 2 5) (by simp) with h37 | h37
                                              · linarith only [h37, h5, hlam]
                                              · linarith only [h10, h37, hlam]
                                      · linarith only [h0, h30, hlam]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h10, h20, h5, h9, hlam, p28_2]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h10, h5, h9, hlam, p28_2]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h0, h10, h20, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h0, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h0, h10, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h0, h10, h20, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h10, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h3, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h8, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h20, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h22, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h4, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h9, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h0, h10, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h24, hlam, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h5, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h0, h5, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      rcases p28_3 (m.d 0 2) (by simp) with h61 | h61
                                      · rcases p28_3 (m.d 1 2) (by simp) with h62 | h62
                                        · linarith only [h10, h62, hlam]
                                        · linarith only [h62, h8, hlam]
                                      · linarith only [h3, h61, hlam]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      rcases p28_3 (m.d 0 2) (by simp) with h66 | h66
                                      · rcases p28_3 (m.d 1 2) (by simp) with h67 | h67
                                        · linarith only [h10, h67, hlam]
                                        · linarith only [h67, h9, hlam]
                                      · linarith only [h4, h66, hlam]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [hlam, p28_0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h72 | h72
                      · linarith only [h72, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h74 | h74
                        · linarith only [h74, h8, h9, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h76 | h76
                          · linarith only [h0, h4, h76, h8, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h78 | h78
                            · linarith only [h0, h4, h74, h78, h8, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h80 | h80
                              · linarith only [h0, h3, h6, h76, h78, h8, h80, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h82 | h82
                                · linarith only [h0, h3, h6, h78, h82, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · linarith only [h8, h82, h9, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h86 | h86
                      · linarith only [h8, h86, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
                          · linarith only [h1, h89, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                              · linarith only [h0, h3, h8, h85, h89, h92, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                              · linarith only [h0, h3, h7, h8, h85, h91, h92, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h3, h6, h8, h85, h91, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h8, h85, h88, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h97 | h97
                      · linarith only [h85, h97, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h100 | h100
                          · linarith only [h1, h100, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h102 | h102
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h103 | h103
                              · linarith only [h0, h100, h103, h3, h99, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h105 | h105
                                · linarith only [h0, h102, h103, h105, h3, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h107 | h107
                                  · linarith only [h105, h107, h85, h99, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
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
                                      linarith only [h103, h3, h7, h8, hlam, p109_2]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      rcases p109_3 (m.d 0 2) (by simp) with h112 | h112
                                      · rcases p109_3 (m.d 1 2) (by simp) with h113 | h113
                                        · linarith only [h0, h113, hlam]
                                        · rcases p109_3 (m.d 2 3) (by simp) with h115 | h115
                                          · linarith only [h115, hlam, p109_0]
                                          · rcases p109_3 (m.d 2 4) (by simp) with h117 | h117
                                            · linarith only [h117, h4, hlam]
                                            · rcases p109_3 (m.d 2 5) (by simp) with h119 | h119
                                              · linarith only [h119, h5, hlam]
                                              · linarith only [h103, h119, hlam]
                                      · linarith only [h112, hlam, p109_0]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      rcases p109_3 (m.d 0 2) (by simp) with h123 | h123
                                      · rcases p109_3 (m.d 1 2) (by simp) with h124 | h124
                                        · linarith only [h0, h124, hlam]
                                        · rcases p109_3 (m.d 2 3) (by simp) with h126 | h126
                                          · linarith only [h126, h3, hlam]
                                          · linarith only [h102, h126, hlam]
                                      · linarith only [h123, hlam, p109_0]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [h0, h97, hc01, hlam, hphi, ht0b, ht5b, p109_1, u5ehi1]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [h0, hlam, p109_0]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [hlam, p109_0]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [h8, hlam, p109_0]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [h85, hlam, p109_0]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [h97, hlam, p109_0]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [h3, hlam, p109_0]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [h0, h103, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p109_1]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [hlam, p109_0]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [h0, h103, h3, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p109_1]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [h103, hlam, p109_0]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [h4, hlam, p109_0]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [h0, h102, h103, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p109_1]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [h102, hlam, p109_1]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [hlam, p109_0]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [h105, hlam, p109_1]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [h5, hlam, p109_0]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      rcases p109_3 (m.d 0 2) (by simp) with h147 | h147
                                      · rcases p109_3 (m.d 1 2) (by simp) with h148 | h148
                                        · linarith only [h148, hlam, p109_0]
                                        · rcases p109_3 (m.d 2 3) (by simp) with h150 | h150
                                          · linarith only [h103, h150, hlam]
                                          · linarith only [h150, h8, hlam]
                                      · linarith only [h0, h147, hlam]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [h0, h5, h8, h99, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p109_1]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [h0, h103, h3, h7, h85, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p109_1]
                                    · have p109_0 := h109c.1
                                      have p109_1 := h109c.2.1
                                      have p109_2 := h109c.2.2.1
                                      have p109_3 := h109c.2.2.2
                                      linarith only [hlam, p109_0]
                            · linarith only [h1, h102, h8, h99, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h158 | h158
                          · linarith only [h1, h158, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h160 | h160
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h161 | h161
                              · linarith only [h0, h158, h161, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                              · linarith only [h160, h161, h99, hc13, hc35, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h164 | h164
                              · linarith only [h160, h164, h3, h6, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h166 | h166
                                · linarith only [h0, h160, h166, h3, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h168 | h168
                                  · linarith only [h0, h168, h3, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · linarith only [h160, h168, h8, hc12, hc45, hlam, hphi, ht23, ht34]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h171 | h171
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h172 | h172
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h173 | h173
                      · linarith only [h0, h173, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h175 | h175
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h176 | h176
                          · linarith only [h176, h7, hc13, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h178 | h178
                            · linarith only [h0, h171, h173, h178, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h178, h6, h7, hc23, hc35, hlam, hphi]
                        · linarith only [h175, h6, h7, hc13, hc35, hlam, hphi]
                    · linarith only [h171, h172, h4, h6, h7, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h183 | h183
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h184 | h184
                      · linarith only [h171, h184, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h186 | h186
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h187 | h187
                          · linarith only [h171, h187, h3, h7, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h189 | h189
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h190 | h190
                              · linarith only [h190, h3, h7, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h192 | h192
                                · linarith only [h171, h183, h192, h3, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h194 | h194
                                  · linarith only [h171, h183, h184, h187, h189, h192, h194, h3, h7, hc13, hc35, hlam, hphi]
                                  · linarith only [h171, h183, h189, h194, h3, h7, hc34, hc45, hlam, hphi]
                            · linarith only [h171, h189, h6, h7, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h171, h183, h186, h6, h7, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h199 | h199
                      · linarith only [h171, h199, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h201 | h201
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h202 | h202
                          · linarith only [h171, h202, h3, h7, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h204 | h204
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h205 | h205
                              · linarith only [h205, h3, h7, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h207 | h207
                                · linarith only [h207, h4, h6, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h209 | h209
                                  · linarith only [h171, h183, h201, h207, h209, h3, h7, hc12, hc35, hlam, hphi, ht23]
                                  · rcases h2bigk with h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      rcases p211_3 (m.d 0 2) (by simp) with h213 | h213
                                      · rcases p211_3 (m.d 1 2) (by simp) with h214 | h214
                                        · linarith only [h0, h214, hlam]
                                        · rcases p211_3 (m.d 2 3) (by simp) with h216 | h216
                                          · linarith only [h216, h3, hlam]
                                          · linarith only [h171, h216, hlam]
                                      · linarith only [h0, h213, hlam]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      rcases p211_3 (m.d 0 2) (by simp) with h220 | h220
                                      · rcases p211_3 (m.d 1 2) (by simp) with h221 | h221
                                        · linarith only [h0, h221, hlam]
                                        · rcases p211_3 (m.d 2 3) (by simp) with h223 | h223
                                          · linarith only [h223, hlam, p211_0]
                                          · rcases p211_3 (m.d 2 4) (by simp) with h225 | h225
                                            · linarith only [h225, h4, hlam]
                                            · rcases p211_3 (m.d 2 5) (by simp) with h227 | h227
                                              · linarith only [h227, h5, hlam]
                                              · linarith only [h205, h227, hlam]
                                      · linarith only [h220, hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      rcases p211_3 (m.d 0 2) (by simp) with h231 | h231
                                      · rcases p211_3 (m.d 1 2) (by simp) with h232 | h232
                                        · linarith only [h0, h232, hlam]
                                        · rcases p211_3 (m.d 2 3) (by simp) with h234 | h234
                                          · linarith only [h234, h3, hlam]
                                          · linarith only [h204, h234, hlam]
                                      · linarith only [h231, hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h0, h199, hc01, hlam, hphi, ht0b, ht5b, p211_1, u5ehi1]
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
                                      linarith only [h171, hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h183, hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h199, hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h3, hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h209, h3, h7, hc12, hc45, hlam, hphi, ht23, ht34, p211_1]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h183, h209, h3, h7, hc12, hc45, hlam, hphi, ht23, ht34, p211_1]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h205, hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h4, hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h209, h4, h6, h7, hc12, hc45, hlam, hphi, ht23, ht34, p211_1]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h204, hlam, p211_1]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h207, hlam, p211_1]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h5, hlam, p211_0]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      rcases p211_3 (m.d 0 2) (by simp) with h255 | h255
                                      · rcases p211_3 (m.d 1 2) (by simp) with h256 | h256
                                        · linarith only [h256, hlam, p211_0]
                                        · rcases p211_3 (m.d 2 3) (by simp) with h258 | h258
                                          · linarith only [h205, h258, hlam]
                                          · linarith only [h171, h258, hlam]
                                      · linarith only [h0, h255, hlam]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h0, h171, h201, h209, h5, h6, h7, hc01, hc34, hc45, hlam, hphi, p211_1, u0ehi3]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [h0, h183, h209, h5, h6, h7, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p211_1, u0ehi3]
                                    · have p211_0 := h211c.1
                                      have p211_1 := h211c.2.1
                                      have p211_2 := h211c.2.2.1
                                      have p211_3 := h211c.2.2.2
                                      linarith only [hlam, p211_0]
                            · linarith only [h1, h171, h201, h204, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h201, h6, h7, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h267 | h267
                · linarith only [h267, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h269 | h269
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h270 | h270
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                      · linarith only [h0, h271, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h273 | h273
                        · linarith only [h273, h6, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h275 | h275
                          · linarith only [h0, h267, h270, h271, h273, h275, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h277 | h277
                            · linarith only [h277, h6, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h279 | h279
                              · linarith only [h267, h270, h271, h277, h279, h5, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h281 | h281
                                · linarith only [h0, h270, h271, h281, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h283 | h283
                                  · linarith only [h270, h271, h277, h281, h283, hc23, hc34, hlam, hphi]
                                  · linarith only [h283, h6, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h286 | h286
                      · linarith only [h0, h270, h286, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h288 | h288
                        · linarith only [h0, h269, h270, h288, h4, h6, hc01, hlam, hphi, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h290 | h290
                          · linarith only [h0, h267, h269, h270, h290, h4, hc01, hlam, hphi, u0ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h292 | h292
                            · linarith only [h0, h269, h270, h292, h4, h6, hc01, hlam, hphi, u0ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h294 | h294
                              · linarith only [h0, h267, h269, h270, h294, h4, hc01, hlam, hphi, u0ehi2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h296 | h296
                                · linarith only [h0, h296, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · linarith only [h269, h270, h296, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h299 | h299
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h300 | h300
                      · linarith only [h269, h3, h300, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h302 | h302
                        · linarith only [h269, h299, h3, h302, h6, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h269, h299, h302, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h305 | h305
                      · linarith only [h269, h3, h305, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h307 | h307
                        · linarith only [h307, h6, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h309 | h309
                          · linarith only [h267, h269, h3, h309, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h311 | h311
                            · linarith only [h3, h311, h6, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h313 | h313
                              · linarith only [h267, h3, h313, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h315 | h315
                                · linarith only [h315, h4, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h317 | h317
                                  · linarith only [h299, h315, h317, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h317, h6, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h320 | h320
              · rcases m.htr 0 3 5 (by decide) (by decide) with h321 | h321
                · linarith only [h3, h321, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h323 | h323
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h324 | h324
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h325 | h325
                      · linarith only [h325, h5, hc12, hlam, hphi, ht01, u0ehi1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h327 | h327
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h328 | h328
                          · linarith only [h1, h321, h328, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h330 | h330
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h331 | h331
                              · linarith only [h0, h320, h321, h323, h331, h5, hc25, hlam, hphi, ht01, ht12, u0ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h333 | h333
                                · linarith only [h0, h323, h330, h331, h333, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                                · linarith only [h0, h323, h330, h333, h5, hc34, hc45, hlam, hphi]
                            · linarith only [h320, h321, h330, hc23, hc35, hlam, hphi]
                        · linarith only [h320, h321, h327, hc13, hc35, hlam, hphi]
                    · linarith only [h324, h4, h5, hc12, hc25, hlam, hphi]
                  · linarith only [h3, h323, h5, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h340 | h340
                · linarith only [h320, h340, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h342 | h342
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h343 | h343
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h344 | h344
                      · linarith only [h0, h344, h5, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h346 | h346
                        · linarith only [h320, h346, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h348 | h348
                          · linarith only [h1, h340, h348, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h350 | h350
                            · linarith only [h0, h320, h342, h350, h5, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h352 | h352
                              · linarith only [h0, h340, h343, h350, h352, h5, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h354 | h354
                                · linarith only [h0, h343, h352, h354, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h356 | h356
                                  · linarith only [h0, h343, h350, h354, h356, h5, hc23, hc34, hlam, hphi]
                                  · linarith only [h320, h356, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                    · linarith only [h343, h4, h5, hc12, hc25, hlam, hphi]
                  · linarith only [h3, h342, h5, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h361 | h361
            · linarith only [h361, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h363 | h363
              · linarith only [h3, h363, h4, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h365 | h365
                · linarith only [h363, h365, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h367 | h367
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h368 | h368
                    · linarith only [h368, h4, hc12, hlam, hphi, ht01, u0ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h370 | h370
                      · linarith only [h0, h361, h370, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h372 | h372
                        · linarith only [h1, h363, h372, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
                          · linarith only [h1, h365, h374, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h376 | h376
                            · linarith only [h363, h376, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h378 | h378
                              · linarith only [h0, h365, h367, h378, hc02, hlam, hphi, u0ehi2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h380 | h380
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h381 | h381
                                  · rcases h2bigk with h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [hlam, p382_0]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h361, h376, h380, hc12, hc34, hlam, hphi, ht23, p382_1]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h361, h376, h380, hc23, hc34, hlam, hphi, p382_1]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h4, hlam, p382_0]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h361, hlam, p382_0]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h0, hlam, p382_0]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [hlam, p382_0]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h0, h361, h376, h380, hc23, hc34, hlam, hphi, p382_1]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h368, hlam, p382_0]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h370, hlam, p382_0]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h3, hlam, p382_0]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h367, hlam, p382_0]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [hlam, p382_0]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h376, hlam, p382_0]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h378, hlam, p382_0]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h376, hc34, hlam, hphi, ht01, ht12, ht23, p382_1, u0ehi1]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h367, h376, hc23, hc34, hlam, hphi, p382_1]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      rcases p382_3 (m.d 0 2) (by simp) with h400 | h400
                                      · linarith only [h4, h400, hlam]
                                      · linarith only [h3, h400, hlam]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [hlam, p382_0]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h376, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p382_1, u5ehi2]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h3, hc25, hlam, hphi, ht01, ht12, p382_1, u0ehi2]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h367, h378, hc23, hc35, hlam, hphi, p382_1]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      rcases p382_3 (m.d 0 2) (by simp) with h407 | h407
                                      · linarith only [h361, h407, hlam]
                                      · linarith only [h3, h407, hlam]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [h380, hlam, p382_0]
                                    · have p382_0 := h382c.1
                                      have p382_1 := h382c.2.1
                                      have p382_2 := h382c.2.2.1
                                      have p382_3 := h382c.2.2.2
                                      linarith only [hlam, p382_0]
                                  · linarith only [h376, h380, h381, hlam]
                                · linarith only [h3, h380, h4, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                  · linarith only [h3, h367, h4, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h415 | h415
          · rcases m.htr 0 2 5 (by decide) (by decide) with h416 | h416
            · linarith only [h3, h416, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h418 | h418
              · rcases m.htr 0 3 5 (by decide) (by decide) with h419 | h419
                · rcases m.htr 1 2 3 (by decide) (by decide) with h420 | h420
                  · linarith only [h3, h420, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h422 | h422
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h423 | h423
                      · linarith only [h0, h416, h423, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h425 | h425
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h426 | h426
                          · linarith only [h1, h426, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h428 | h428
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h429 | h429
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h430 | h430
                                · linarith only [h419, h420, h422, h426, h430, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h432 | h432
                                  · linarith only [h3, h415, h416, h419, h420, h422, h426, h428, h430, h432, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                                  · rcases h2bigk with h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [hlam, p434_0]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [h416, h430, hc12, hc45, hlam, hphi, ht23, ht34, p434_1]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [h3, hlam, p434_0]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [h416, h428, h430, hc34, hc45, hlam, hphi, p434_1]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [h416, hlam, p434_0]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [h0, hlam, p434_0]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [hlam, p434_0]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [h420, hlam, p434_0]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [h0, h416, h428, h430, hc34, hc45, hlam, hphi, p434_1]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [h423, hlam, p434_0]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht01, ht12, p434_1, u0ehi1]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      rcases p434_3 (m.d 0 2) (by simp) with h446 | h446
                                      · linarith only [h3, h446, hlam]
                                      · linarith only [h0, h446, hlam]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [hlam, p434_0]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [h3, h419, h420, h422, h426, hlam, p434_2]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p434_1, u5ehi2]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [h415, hlam, p434_0]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [h422, hlam, p434_0]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [h428, hlam, p434_1]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [hlam, p434_0]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [h430, hlam, p434_1]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [h415, hc25, hlam, hphi, ht01, ht12, p434_1, u0ehi3]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [h422, h428, h430, hc34, hc45, hlam, hphi, p434_1]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [h429, hlam, p434_1]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      rcases p434_3 (m.d 0 2) (by simp) with h460 | h460
                                      · linarith only [h416, h460, hlam]
                                      · linarith only [h415, h460, hlam]
                                    · have p434_0 := h434c.1
                                      have p434_1 := h434c.2.1
                                      have p434_2 := h434c.2.2.1
                                      have p434_3 := h434c.2.2.2
                                      linarith only [hlam, p434_0]
                              · linarith only [h3, h419, h429, hlam]
                            · linarith only [h3, h419, h420, h422, h426, h428, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h420, h422, h425, hlam]
                    · linarith only [h3, h415, h422, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h468 | h468
                  · linarith only [h0, h3, h468, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h470 | h470
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h471 | h471
                      · linarith only [h0, h471, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h473 | h473
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h474 | h474
                          · linarith only [h1, h419, h474, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h476 | h476
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h477 | h477
                              · linarith only [h3, h419, h477, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                              · linarith only [h3, h415, h477, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                            · linarith only [h3, h415, h476, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h418, h419, h468, h470, h473, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h3, h415, h419, h470, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h3, h415, h418, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h484 | h484
            · linarith only [h415, h484, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h486 | h486
              · rcases m.htr 0 3 5 (by decide) (by decide) with h487 | h487
                · rcases m.htr 1 2 3 (by decide) (by decide) with h488 | h488
                  · linarith only [h3, h488, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h490 | h490
                    · linarith only [h0, h415, h490, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h492 | h492
                      · linarith only [h0, h484, h492, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h494 | h494
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h495 | h495
                          · linarith only [h1, h495, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h497 | h497
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h498 | h498
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h499 | h499
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h500 | h500
                                  · linarith only [h487, h494, h495, h500, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases h2bigk with h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [hlam, p502_0]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [h484, hc12, hc25, hlam, hphi, p502_1]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [h3, hlam, p502_0]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [h415, hlam, p502_0]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [h484, hlam, p502_0]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [h0, hlam, p502_0]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [hlam, p502_0]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [h488, hlam, p502_0]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [h490, hlam, p502_0]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [h492, hlam, p502_0]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht01, ht12, p502_1, u0ehi1]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      rcases p502_3 (m.d 0 2) (by simp) with h514 | h514
                                      · linarith only [h3, h514, hlam]
                                      · linarith only [h0, h514, hlam]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [hlam, p502_0]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [h495, h499, h500, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p502_1]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p502_1, u5ehi2]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [hc24, hlam, hphi, ht01, ht12, p502_1, u0ehi1]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      rcases p502_3 (m.d 0 2) (by simp) with h521 | h521
                                      · linarith only [h415, h521, hlam]
                                      · linarith only [h0, h521, hlam]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [h497, hlam, p502_1]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [hlam, p502_0]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [h484, h497, hc23, hlam, hphi, ht01, ht12, p502_1, u0ehi1]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht01, ht12, p502_1, u0ehi1]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      rcases p502_3 (m.d 0 2) (by simp) with h528 | h528
                                      · linarith only [h484, h528, hlam]
                                      · linarith only [h0, h528, hlam]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [h498, hlam, p502_1]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [h499, hlam, p502_0]
                                    · have p502_0 := h502c.1
                                      have p502_1 := h502c.2.1
                                      have p502_2 := h502c.2.2.1
                                      have p502_3 := h502c.2.2.2
                                      linarith only [hlam, p502_0]
                                · linarith only [h415, h499, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                              · linarith only [h3, h498, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                            · linarith only [h3, h487, h494, h497, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h537 | h537
                          · linarith only [h486, h494, h537, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h539 | h539
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h540 | h540
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h541 | h541
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h542 | h542
                                  · linarith only [h3, h486, h542, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                  · linarith only [h488, h494, h539, h541, h542, hc12, hc23, hlam, hphi]
                                · linarith only [h415, h541, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                              · linarith only [h3, h540, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                            · linarith only [h3, h487, h537, h539, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h548 | h548
                  · linarith only [h3, h548, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h550 | h550
                    · linarith only [h415, h550, hc12, hlam, hphi, ht01, u0ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h552 | h552
                      · linarith only [h0, h3, h552, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h554 | h554
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h555 | h555
                          · linarith only [h1, h487, h555, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h557 | h557
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h558 | h558
                              · linarith only [h415, h486, h487, h558, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                              · linarith only [h3, h558, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                            · linarith only [h1, h3, h554, h557, hc03, hlam, hphi, u0ehi1]
                        · linarith only [h486, h487, h554, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h563 | h563
                · linarith only [h486, h563, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h565 | h565
                  · linarith only [h0, h3, h565, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h567 | h567
                    · linarith only [h415, h567, hc12, hlam, hphi, ht01, u0ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h569 | h569
                      · linarith only [h0, h484, h569, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h571 | h571
                        · linarith only [h1, h486, h571, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h573 | h573
                          · linarith only [h1, h563, h573, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h575 | h575
                            · linarith only [h486, h575, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                            · linarith only [h3, h575, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h578 | h578
        · rcases m.htr 0 2 4 (by decide) (by decide) with h579 | h579
          · rcases m.htr 0 2 5 (by decide) (by decide) with h580 | h580
            · linarith only [h0, h2, h580, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h582 | h582
              · rcases m.htr 0 3 5 (by decide) (by decide) with h583 | h583
                · linarith only [h1, h2, h583, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h585 | h585
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h586 | h586
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h587 | h587
                      · linarith only [h0, h2, h580, h587, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h589 | h589
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h590 | h590
                          · linarith only [h0, h2, h582, h583, h585, h587, h590, hc25, hlam, hphi, ht01, ht12, u0ehi3]
                          · linarith only [h0, h2, h585, h590, hc23, hc35, hlam, hphi]
                        · linarith only [h582, h583, h589, hc13, hc35, hlam, hphi]
                    · linarith only [h579, h580, h586, hc12, hc25, hlam, hphi]
                  · linarith only [h578, h580, h585, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h596 | h596
                · linarith only [h582, h596, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h598 | h598
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h599 | h599
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h600 | h600
                      · linarith only [h580, h600, hc12, hlam, hphi, ht01, u0ehi1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h602 | h602
                        · linarith only [h582, h602, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h604 | h604
                          · linarith only [h0, h2, h596, h599, h600, h602, h604, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                          · linarith only [h0, h2, h598, h604, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h2, h579, h598, h599, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h578, h580, h598, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h609 | h609
            · linarith only [h0, h2, h609, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h611 | h611
              · linarith only [h578, h579, h611, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h613 | h613
                · linarith only [h578, h579, h613, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h615 | h615
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h616 | h616
                    · linarith only [h0, h2, h579, h616, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h618 | h618
                      · linarith only [h0, h2, h578, h609, h618, hc15, hlam, hphi, ht01, u0ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h620 | h620
                        · linarith only [h611, h620, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h622 | h622
                          · linarith only [h0, h2, h613, h615, h618, h622, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                          · linarith only [h0, h2, h615, h622, hc23, hc35, hlam, hphi]
                  · linarith only [h578, h579, h615, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h626 | h626
          · rcases m.htr 0 2 5 (by decide) (by decide) with h627 | h627
            · linarith only [h1, h2, h578, h627, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h629 | h629
              · rcases m.htr 0 3 5 (by decide) (by decide) with h630 | h630
                · linarith only [h1, h2, h630, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h632 | h632
                  · linarith only [h0, h2, h578, h632, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h634 | h634
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h635 | h635
                      · linarith only [h1, h2, h626, h627, h632, h635, hc15, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h637 | h637
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h638 | h638
                          · linarith only [h1, h2, h630, h635, h638, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h640 | h640
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h641 | h641
                              · linarith only [h1, h2, h632, h638, h641, hc12, hc23, hlam, hphi]
                              · linarith only [h578, h626, h641, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                            · linarith only [h578, h626, h640, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h1, h2, h629, h632, h635, h637, hc12, hc25, hlam, hphi]
                    · linarith only [h578, h626, h634, hc12, hc23, hlam, hphi]
              · linarith only [h578, h626, h629, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h648 | h648
            · linarith only [h1, h2, h578, h648, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h650 | h650
              · rcases m.htr 0 3 5 (by decide) (by decide) with h651 | h651
                · linarith only [h1, h2, h651, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h653 | h653
                  · linarith only [h0, h2, h578, h653, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h655 | h655
                    · linarith only [h626, h655, hc12, hlam, hphi, ht01, u0ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h657 | h657
                      · linarith only [h1, h2, h653, h657, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h659 | h659
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h660 | h660
                          · linarith only [h1, h2, h651, h657, h660, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h662 | h662
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h663 | h663
                              · linarith only [h1, h2, h655, h659, h660, h663, hc12, hc23, hlam, hphi]
                              · linarith only [h578, h663, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                            · linarith only [h578, h659, h662, hc13, hlam, hphi, ht01, u0ehi1]
                        · linarith only [h650, h651, h653, h659, hc12, hc35, hlam, hphi, ht23]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h668 | h668
                · linarith only [h650, h668, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h670 | h670
                  · linarith only [h578, h670, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h672 | h672
                    · linarith only [h1, h2, h626, h670, h672, hc15, hlam, hphi, ht01, u0ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h674 | h674
                      · linarith only [h1, h2, h670, h674, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h676 | h676
                        · linarith only [h1, h2, h650, h674, h676, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h678 | h678
                          · linarith only [h1, h2, h578, h668, h674, h678, hc25, hlam, hphi, ht01, ht12, u0ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h680 | h680
                            · linarith only [h578, h650, h680, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                            · linarith only [h578, h680, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h683 | h683
      · linarith only [h1, h683, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h685 | h685
        · linarith only [h0, h1, h685, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h687 | h687
          · rcases m.htr 0 2 5 (by decide) (by decide) with h688 | h688
            · linarith only [h0, h1, h688, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h690 | h690
              · rcases m.htr 0 3 5 (by decide) (by decide) with h691 | h691
                · rcases m.htr 1 2 3 (by decide) (by decide) with h692 | h692
                  · linarith only [h685, h692, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h694 | h694
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h695 | h695
                      · linarith only [h0, h1, h687, h688, h692, h695, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h697 | h697
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h698 | h698
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h699 | h699
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h700 | h700
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h701 | h701
                                · linarith only [h0, h683, h692, h694, h698, h701, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                · linarith only [h0, h683, h694, h695, h701, hc24, hc45, hlam, hphi]
                              · linarith only [h0, h1, h691, h692, h694, h699, h700, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h683, h692, h694, h698, h699, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1, h691, h698, hlam]
                        · linarith only [h1, h691, h697, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · linarith only [h0, h1, h687, h692, h694, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h709 | h709
                  · linarith only [h0, h1, h691, h709, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h711 | h711
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h712 | h712
                      · linarith only [h0, h1, h691, h712, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h714 | h714
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h715 | h715
                          · linarith only [h0, h1, h691, h709, h715, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h711, h715, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h711, h714, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h685, h687, h711, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1, h687, h690, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h721 | h721
            · linarith only [h0, h1, h721, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h723 | h723
              · rcases m.htr 0 3 5 (by decide) (by decide) with h724 | h724
                · rcases m.htr 1 2 3 (by decide) (by decide) with h725 | h725
                  · linarith only [h685, h725, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h727 | h727
                    · linarith only [h0, h1, h687, h725, h727, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h729 | h729
                      · linarith only [h0, h1, h721, h725, h729, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h731 | h731
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h732 | h732
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h733 | h733
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h734 | h734
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h735 | h735
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h736 | h736
                                  · linarith only [h723, h736, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases h2bigk with h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h0, h683, h729, h733, h735, hc12, hc23, hlam, hphi, p738_1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h685, hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h687, hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h721, hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h0, hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h725, hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h727, hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h729, hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht01, ht12, p738_1, u0ehi1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      rcases p738_3 (m.d 0 2) (by simp) with h750 | h750
                                      · linarith only [h685, h750, hlam]
                                      · linarith only [h0, h750, hlam]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h683, h729, h735, hc01, hc23, hlam, hphi, ht12, p738_1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h0, h683, h729, hc23, hlam, hphi, ht01, ht12, p738_1, u0ehi1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [hc24, hlam, hphi, ht01, ht12, p738_1, u0ehi1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      rcases p738_3 (m.d 0 2) (by simp) with h757 | h757
                                      · linarith only [h687, h757, hlam]
                                      · linarith only [h0, h757, hlam]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h733, hlam, p738_1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h0, h683, h729, h733, hc23, hlam, hphi, ht01, ht12, p738_1, u0ehi1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht01, ht12, p738_1, u0ehi1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      rcases p738_3 (m.d 0 2) (by simp) with h764 | h764
                                      · linarith only [h721, h764, hlam]
                                      · linarith only [h0, h764, hlam]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h734, hlam, p738_1]
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
                                · linarith only [h687, h735, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                              · linarith only [h0, h1, h725, h734, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                            · linarith only [h1, h724, h725, h733, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · linarith only [h1, h724, h732, hlam]
                        · linarith only [h1, h723, h724, h731, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h775 | h775
                  · linarith only [h0, h1, h724, h775, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h777 | h777
                    · linarith only [h0, h1, h687, h724, h777, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h779 | h779
                      · linarith only [h0, h1, h724, h779, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h781 | h781
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h782 | h782
                          · linarith only [h0, h1, h724, h775, h782, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h782, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h0, h1, h723, h781, hc03, hlam, hphi, u0ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h786 | h786
                · linarith only [h723, h786, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h788 | h788
                  · linarith only [h0, h1, h723, h788, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h790 | h790
                    · linarith only [h0, h1, h687, h723, h790, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h792 | h792
                      · linarith only [h0, h1, h723, h792, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h794 | h794
                        · linarith only [h0, h1, h723, h788, h794, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h794, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h797 | h797
    · rcases m.htr 0 1 5 (by decide) (by decide) with h798 | h798
      · linarith only [h0, h798, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h800 | h800
        · rcases m.htr 0 2 4 (by decide) (by decide) with h801 | h801
          · rcases m.htr 0 2 5 (by decide) (by decide) with h802 | h802
            · rcases m.htr 0 3 4 (by decide) (by decide) with h803 | h803
              · rcases m.htr 0 3 5 (by decide) (by decide) with h804 | h804
                · linarith only [h0, h797, h804, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h806 | h806
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h807 | h807
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h808 | h808
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h809 | h809
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h810 | h810
                          · linarith only [h797, h798, h804, h808, h810, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h812 | h812
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h813 | h813
                              · linarith only [h797, h798, h806, h810, h813, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h815 | h815
                                · linarith only [h797, h798, h807, h809, h810, h815, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h817 | h817
                                  · linarith only [h797, h798, h806, h810, h812, h815, h817, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                  · linarith only [h797, h798, h809, h810, h817, hc34, hc45, hlam, hphi]
                            · linarith only [h797, h798, h809, h810, h812, hc23, hc35, hlam, hphi]
                        · linarith only [h803, h804, h809, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h802, h808, hc02, hlam, hphi, u0ehi0]
                    · linarith only [h0, h802, h807, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h0, h806, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h825 | h825
                · linarith only [h797, h798, h825, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h827 | h827
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h828 | h828
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h829 | h829
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h830 | h830
                        · linarith only [h797, h798, h803, h829, h830, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h832 | h832
                          · linarith only [h797, h798, h825, h829, h832, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h834 | h834
                            · linarith only [h797, h798, h803, h827, h832, h834, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h836 | h836
                              · linarith only [h797, h798, h827, h832, h836, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h838 | h838
                                · linarith only [h801, h838, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h840 | h840
                                  · rcases h2bigk with h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [hlam, p841_0]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [h0, hlam, p841_1]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      rcases p841_3 (m.d 0 2) (by simp) with h844 | h844
                                      · rcases p841_3 (m.d 1 2) (by simp) with h845 | h845
                                        · rcases p841_3 (m.d 2 3) (by simp) with h846 | h846
                                          · linarith only [h846, hlam, p841_0]
                                          · rcases p841_3 (m.d 2 4) (by simp) with h848 | h848
                                            · linarith only [h801, h848, hlam]
                                            · linarith only [h834, h848, hlam]
                                        · linarith only [h827, h845, hlam]
                                      · linarith only [h844, hlam, p841_0]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      rcases p841_3 (m.d 0 2) (by simp) with h853 | h853
                                      · rcases p841_3 (m.d 1 2) (by simp) with h854 | h854
                                        · rcases p841_3 (m.d 2 3) (by simp) with h855 | h855
                                          · linarith only [h800, h855, hlam]
                                          · rcases p841_3 (m.d 2 4) (by simp) with h857 | h857
                                            · linarith only [h857, hlam, p841_0]
                                            · rcases p841_3 (m.d 2 5) (by simp) with h859 | h859
                                              · linarith only [h802, h859, hlam]
                                              · linarith only [h838, h859, hlam]
                                        · linarith only [h828, h854, hlam]
                                      · linarith only [h853, hlam, p841_0]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p841_1, u5ehi2]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, p841_1, u0ehi1]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [hlam, p841_0]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      rcases p841_3 (m.d 0 2) (by simp) with h867 | h867
                                      · linarith only [h0, h867, hlam]
                                      · linarith only [h800, h867, hlam]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      rcases p841_3 (m.d 0 2) (by simp) with h870 | h870
                                      · linarith only [h0, h870, hlam]
                                      · linarith only [h801, h870, hlam]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p841_1, u5ehi2]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [h800, hlam, p841_0]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [h827, hlam, p841_0]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [hlam, p841_0]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [h834, hlam, p841_0]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [h836, hlam, p841_0]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [h801, hlam, p841_0]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [h828, hlam, p841_0]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [h838, h840, hc23, hc34, hlam, hphi, p841_1]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [hlam, p841_0]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [h838, hlam, p841_1]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [h802, hlam, p841_0]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [h829, hlam, p841_0]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [h838, h840, hc23, hc34, hlam, hphi, p841_1]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [h834, h838, h840, hc23, hc34, hlam, hphi, p841_1]
                                    · have p841_0 := h841c.1
                                      have p841_1 := h841c.2.1
                                      have p841_2 := h841c.2.2.1
                                      have p841_3 := h841c.2.2.2
                                      linarith only [hlam, p841_0]
                                  · linarith only [h803, h840, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                      · linarith only [h0, h797, h802, h829, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h802, h828, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h0, h802, h827, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h893 | h893
              · rcases m.htr 0 3 5 (by decide) (by decide) with h894 | h894
                · linarith only [h0, h797, h894, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h896 | h896
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h897 | h897
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h898 | h898
                      · linarith only [h0, h802, h898, hc12, hlam, hphi, ht01, u0ehi0]
                      · linarith only [h0, h797, h893, h898, hc25, hlam, hphi, ht01, ht12, u0ehi3]
                    · linarith only [h0, h797, h893, h897, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                  · linarith only [h0, h797, h893, h896, hc23, hlam, hphi, ht01, ht12, u0ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h903 | h903
                · linarith only [h0, h797, h903, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h905 | h905
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h906 | h906
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h907 | h907
                      · linarith only [h0, h802, h907, hc12, hlam, hphi, ht01, u0ehi0]
                      · linarith only [h0, h797, h907, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h0, h797, h801, h906, hc02, hlam, hphi, u0ehi2]
                  · linarith only [h0, h797, h905, hc23, hlam, hphi, ht01, ht12, u0ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h912 | h912
            · linarith only [h801, h912, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h914 | h914
              · linarith only [h0, h797, h801, h914, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h916 | h916
                · linarith only [h0, h797, h801, h916, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h918 | h918
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h919 | h919
                    · linarith only [h0, h801, h919, hc12, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h0, h797, h919, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                  · linarith only [h0, h797, h918, hc23, hlam, hphi, ht01, ht12, u0ehi2]
        · linarith only [h0, h797, h800, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h924 | h924
      · linarith only [h0, h924, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h926 | h926
        · rcases m.htr 0 2 4 (by decide) (by decide) with h927 | h927
          · rcases m.htr 0 2 5 (by decide) (by decide) with h928 | h928
            · rcases m.htr 0 3 4 (by decide) (by decide) with h929 | h929
              · rcases m.htr 0 3 5 (by decide) (by decide) with h930 | h930
                · rcases m.htr 1 2 3 (by decide) (by decide) with h931 | h931
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h932 | h932
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h933 | h933
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h934 | h934
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h935 | h935
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h936 | h936
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h937 | h937
                              · linarith only [h926, h937, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h939 | h939
                                · linarith only [h797, h930, h931, h936, h937, h939, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h941 | h941
                                  · linarith only [h797, h930, h931, h936, h937, h939, h941, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases h2bigk with h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [hlam, p943_0]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [h0, hlam, p943_1]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      rcases p943_3 (m.d 0 2) (by simp) with h946 | h946
                                      · rcases p943_3 (m.d 1 2) (by simp) with h947 | h947
                                        · rcases p943_3 (m.d 2 3) (by simp) with h948 | h948
                                          · linarith only [h948, hlam, p943_0]
                                          · rcases p943_3 (m.d 2 4) (by simp) with h950 | h950
                                            · linarith only [h927, h950, hlam]
                                            · rcases p943_3 (m.d 2 5) (by simp) with h952 | h952
                                              · linarith only [h928, h952, hlam]
                                              · linarith only [h937, h952, hlam]
                                        · linarith only [h931, h947, hlam]
                                      · linarith only [h946, hlam, p943_0]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      rcases p943_3 (m.d 0 2) (by simp) with h957 | h957
                                      · rcases p943_3 (m.d 1 2) (by simp) with h958 | h958
                                        · rcases p943_3 (m.d 2 3) (by simp) with h959 | h959
                                          · linarith only [h926, h959, hlam]
                                          · linarith only [h936, h959, hlam]
                                        · linarith only [h932, h958, hlam]
                                      · linarith only [h957, hlam, p943_0]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [hc02, hlam, hphi, ht0b, ht5b, p943_1, u5ehi2]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, p943_1, u0ehi1]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [hlam, p943_0]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      rcases p943_3 (m.d 0 2) (by simp) with h967 | h967
                                      · linarith only [h0, h967, hlam]
                                      · linarith only [h926, h967, hlam]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      rcases p943_3 (m.d 0 2) (by simp) with h970 | h970
                                      · linarith only [h0, h970, hlam]
                                      · linarith only [h927, h970, hlam]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p943_1, u5ehi2]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [h926, hlam, p943_0]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [h931, hlam, p943_0]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [hlam, p943_0]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [h797, h930, h931, h937, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p943_1]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [h937, hlam, p943_0]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [h927, hlam, p943_0]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [h932, hlam, p943_0]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [h936, hlam, p943_1]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [hlam, p943_0]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [h939, hlam, p943_1]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [h928, hlam, p943_0]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [h933, hlam, p943_0]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [h928, h936, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p943_1]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      rcases p943_3 (m.d 0 2) (by simp) with h987 | h987
                                      · rcases p943_3 (m.d 1 2) (by simp) with h988 | h988
                                        · rcases p943_3 (m.d 2 3) (by simp) with h989 | h989
                                          · linarith only [h937, h989, hlam]
                                          · linarith only [h936, h989, hlam]
                                        · linarith only [h932, h988, hlam]
                                      · linarith only [h927, h987, hlam]
                                    · have p943_0 := h943c.1
                                      have p943_1 := h943c.2.1
                                      have p943_2 := h943c.2.2.1
                                      have p943_3 := h943c.2.2.2
                                      linarith only [hlam, p943_0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h995 | h995
                              · linarith only [h936, h995, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h997 | h997
                                · linarith only [h0, h927, h997, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h999 | h999
                                  · linarith only [h929, h999, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases h2bigk with h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [hlam, p1001_0]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [h0, hlam, p1001_1]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      rcases p1001_3 (m.d 0 2) (by simp) with h1004 | h1004
                                      · rcases p1001_3 (m.d 1 2) (by simp) with h1005 | h1005
                                        · rcases p1001_3 (m.d 2 3) (by simp) with h1006 | h1006
                                          · linarith only [h1006, hlam, p1001_0]
                                          · rcases p1001_3 (m.d 2 4) (by simp) with h1008 | h1008
                                            · linarith only [h1008, h927, hlam]
                                            · linarith only [h1008, h936, hlam]
                                        · linarith only [h1005, h931, hlam]
                                      · linarith only [h1004, hlam, p1001_0]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      rcases p1001_3 (m.d 0 2) (by simp) with h1013 | h1013
                                      · rcases p1001_3 (m.d 1 2) (by simp) with h1014 | h1014
                                        · rcases p1001_3 (m.d 2 3) (by simp) with h1015 | h1015
                                          · linarith only [h1015, h926, hlam]
                                          · rcases p1001_3 (m.d 2 4) (by simp) with h1017 | h1017
                                            · linarith only [h1017, hlam, p1001_0]
                                            · rcases p1001_3 (m.d 2 5) (by simp) with h1019 | h1019
                                              · linarith only [h1019, h928, hlam]
                                              · linarith only [h1019, h997, hlam]
                                        · linarith only [h1014, h932, hlam]
                                      · linarith only [h1013, hlam, p1001_0]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p1001_1, u5ehi2]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [h926, h930, hc12, hlam, hphi, ht01, ht0b, ht5b, p1001_1, u5ehi3]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [hlam, p1001_0]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      rcases p1001_3 (m.d 0 2) (by simp) with h1027 | h1027
                                      · linarith only [h0, h1027, hlam]
                                      · linarith only [h1027, h926, hlam]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      rcases p1001_3 (m.d 0 2) (by simp) with h1030 | h1030
                                      · linarith only [h0, h1030, hlam]
                                      · linarith only [h1030, h927, hlam]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p1001_1, u5ehi2]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [h926, hlam, p1001_0]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [h931, hlam, p1001_0]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [hlam, p1001_0]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [h936, hlam, p1001_0]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [h995, hlam, p1001_0]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [h927, hlam, p1001_0]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [h932, hlam, p1001_0]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [h936, h999, hc23, hc45, hlam, hphi, ht34, p1001_1]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [hlam, p1001_0]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [h997, hlam, p1001_1]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [h928, hlam, p1001_0]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [h933, hlam, p1001_0]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      rcases p1001_3 (m.d 0 2) (by simp) with h1046 | h1046
                                      · rcases p1001_3 (m.d 1 2) (by simp) with h1047 | h1047
                                        · rcases p1001_3 (m.d 2 3) (by simp) with h1048 | h1048
                                          · linarith only [h1048, h995, hlam]
                                          · rcases p1001_3 (m.d 2 4) (by simp) with h1050 | h1050
                                            · linarith only [h1050, h997, hlam]
                                            · linarith only [h1050, h936, hlam]
                                        · linarith only [h1047, h931, hlam]
                                      · linarith only [h1046, h926, hlam]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      rcases p1001_3 (m.d 0 2) (by simp) with h1055 | h1055
                                      · rcases p1001_3 (m.d 1 2) (by simp) with h1056 | h1056
                                        · rcases p1001_3 (m.d 2 3) (by simp) with h1057 | h1057
                                          · linarith only [h1057, h995, hlam]
                                          · rcases p1001_3 (m.d 2 4) (by simp) with h1059 | h1059
                                            · linarith only [h1059, h997, hlam]
                                            · rcases p1001_3 (m.d 2 5) (by simp) with h1061 | h1061
                                              · rcases h3bigk with h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [hlam, p1062_0]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [h797, hlam, p1062_1]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [h930, h936, h995, hlam, p1001_1, p1062_2]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  rcases p1062_3 (m.d 0 3) (by simp) with h1066 | h1066
                                                  · rcases p1062_3 (m.d 1 3) (by simp) with h1067 | h1067
                                                    · rcases p1062_3 (m.d 2 3) (by simp) with h1068 | h1068
                                                      · linarith only [h1068, h926, hlam]
                                                      · rcases p1062_3 (m.d 3 4) (by simp) with h1070 | h1070
                                                        · linarith only [h1070, hlam, p1062_0]
                                                        · rcases p1062_3 (m.d 3 5) (by simp) with h1072 | h1072
                                                          · linarith only [h1072, h930, hlam]
                                                          · linarith only [h1072, h999, hlam]
                                                    · linarith only [h1067, h934, hlam]
                                                  · linarith only [h1066, hlam, p1062_0]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [h797, h931, h936, h995, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1001_1, p1062_1]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [h931, hc12, hlam, hphi, ht01, p1062_1, u0ehi2]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [hlam, p1062_0]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [h797, h930, h936, h995, hlam, p1001_1, p1062_2]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  rcases p1062_3 (m.d 0 3) (by simp) with h1081 | h1081
                                                  · linarith only [h1081, h797, hlam]
                                                  · linarith only [h1081, h929, hlam]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [h936, h995, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1001_1, p1062_1]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [h926, hlam, p1062_0]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [h931, hlam, p1062_0]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [hlam, p1062_0]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [h936, hlam, p1062_0]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [h995, hlam, p1062_0]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [h929, hlam, p1062_0]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [h934, hlam, p1062_0]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [h999, hc23, hc45, hlam, hphi, ht34, p1062_1]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [hlam, p1062_0]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [h999, hlam, p1062_1]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [h930, hlam, p1062_0]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [h935, hlam, p1062_0]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  rcases p1062_3 (m.d 0 3) (by simp) with h1097 | h1097
                                                  · rcases p1062_3 (m.d 1 3) (by simp) with h1098 | h1098
                                                    · rcases p1062_3 (m.d 2 3) (by simp) with h1099 | h1099
                                                      · linarith only [h1099, hlam, p1062_0]
                                                      · rcases p1062_3 (m.d 3 4) (by simp) with h1101 | h1101
                                                        · linarith only [h1101, h999, hlam]
                                                        · linarith only [h1101, h936, hlam]
                                                    · linarith only [h1098, h931, hlam]
                                                  · linarith only [h1097, h926, hlam]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [h930, h936, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1062_1]
                                                · have p1062_0 := h1062c.1
                                                  have p1062_1 := h1062c.2.1
                                                  have p1062_2 := h1062c.2.2.1
                                                  have p1062_3 := h1062c.2.2.2
                                                  linarith only [hlam, p1062_0]
                                              · linarith only [h1061, h997, hlam]
                                        · linarith only [h1056, h932, hlam]
                                      · linarith only [h1055, h927, hlam]
                                    · have p1001_0 := h1001c.1
                                      have p1001_1 := h1001c.2.1
                                      have p1001_2 := h1001c.2.2.1
                                      have p1001_3 := h1001c.2.2.2
                                      linarith only [hlam, p1001_0]
                          · linarith only [h797, h930, h935, hlam]
                        · linarith only [h797, h930, h934, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                      · linarith only [h0, h933, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                    · linarith only [h0, h926, h930, h932, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h926, h930, h931, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1117 | h1117
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1118 | h1118
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1119 | h1119
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1120 | h1120
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1121 | h1121
                          · linarith only [h1121, h930, hc13, hlam, hphi, ht01, u0ehi2]
                          · linarith only [h1121, h797, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                        · linarith only [h1120, h797, h929, hc03, hlam, hphi, u0ehi0]
                      · linarith only [h0, h1119, h928, hlam]
                    · linarith only [h0, h1118, h927, h928, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h1117, h926, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1128 | h1128
                · linarith only [h1128, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1130 | h1130
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1131 | h1131
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1132 | h1132
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1133 | h1133
                        · linarith only [h1133, h929, hc13, hlam, hphi, ht01, u0ehi2]
                        · linarith only [h1133, h797, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                      · linarith only [h0, h1132, h928, hlam]
                    · linarith only [h0, h1131, h927, hlam]
                  · linarith only [h0, h1130, h926, h928, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1139 | h1139
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1140 | h1140
                · linarith only [h1140, h926, h928, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1142 | h1142
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1143 | h1143
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1144 | h1144
                      · linarith only [h1144, h928, hc12, hlam, hphi, ht01, u0ehi1]
                      · linarith only [h0, h1144, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                    · linarith only [h1142, h1143, h797, h927, hc02, hlam, hphi, u0ehi0]
                  · linarith only [h1142, h926, h928, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1149 | h1149
                · linarith only [h1139, h1149, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1151 | h1151
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1152 | h1152
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1153 | h1153
                      · linarith only [h1153, h928, hc12, hlam, hphi, ht01, u0ehi1]
                      · linarith only [h0, h1153, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                    · linarith only [h1151, h1152, h797, h927, hc02, hlam, hphi, u0ehi0]
                  · linarith only [h1151, h926, h928, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1158 | h1158
            · linarith only [h1158, h927, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1160 | h1160
              · linarith only [h1160, h926, h927, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1162 | h1162
                · linarith only [h1162, h926, h927, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1164 | h1164
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1165 | h1165
                    · linarith only [h1165, h927, hc12, hlam, hphi, ht01, u0ehi1]
                    · linarith only [h0, h1165, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                  · linarith only [h0, h1164, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1169 | h1169
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1170 | h1170
            · linarith only [h1170, h926, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1172 | h1172
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1173 | h1173
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1174 | h1174
                  · linarith only [h1174, h926, hc12, hlam, hphi, ht01, u0ehi1]
                  · linarith only [h0, h1174, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1177 | h1177
                  · linarith only [h0, h1177, h926, hc12, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h0, h1177, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h1169, h1172, h926, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1181 | h1181
            · linarith only [h1169, h1181, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1183 | h1183
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1184 | h1184
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1185 | h1185
                  · linarith only [h1185, h926, hc12, hlam, hphi, ht01, u0ehi1]
                  · linarith only [h0, h1185, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1188 | h1188
                  · linarith only [h0, h1188, h926, hc12, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h0, h1188, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1191 | h1191
                · linarith only [h1183, h1191, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1193 | h1193
                  · linarith only [h0, h1193, h926, hc12, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h0, h1193, hc23, hlam, hphi, ht01, ht12, u0ehi0]

end R2N4
