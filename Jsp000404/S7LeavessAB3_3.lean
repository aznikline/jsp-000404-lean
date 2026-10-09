import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5002000 in
theorem n7l_sAB3_H_I_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h3bigk := hb3.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                                      · linarith only [h0, h15, h18, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                      · linarith only [h18, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h14, h17, h3, hc24, hlam, hphi, ht45, u5elo0]
                                  · linarith only [h16, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                                  · linarith only [h0, h12, h15, h23, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h23, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h14, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h13, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                                · linarith only [h0, h12, h28, h30, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h32 | h32
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h34 | h34
                                      · rcases h3bigk with h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [hlam, p35_0]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          rcases p35_3 (m.d 0 3) (by simp) with h37 | h37
                                          · rcases p35_3 (m.d 1 3) (by simp) with h38 | h38
                                            · linarith only [h1, h38, hlam]
                                            · rcases p35_3 (m.d 2 3) (by simp) with h40 | h40
                                              · linarith only [h4, h40, hlam]
                                              · rcases p35_3 (m.d 3 4) (by simp) with h42 | h42
                                                · linarith only [h42, h6, hlam]
                                                · linarith only [h12, h42, hlam]
                                          · linarith only [h1, h37, hlam]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          rcases p35_3 (m.d 0 3) (by simp) with h46 | h46
                                          · rcases p35_3 (m.d 1 3) (by simp) with h47 | h47
                                            · linarith only [h1, h47, hlam]
                                            · linarith only [h47, h9, hlam]
                                          · linarith only [h4, h46, hlam]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [h0, h12, h32, h34, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p35_1]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [h12, h32, h6, h9, hlam, p35_2]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [h1, hlam, p35_0]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [hlam, p35_0]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [h12, h32, h34, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p35_1]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [h12, hlam, p35_0]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [h0, h12, h34, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p35_1]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [h4, hlam, p35_0]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [h9, hlam, p35_0]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [hlam, p35_0]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [h30, hlam, p35_0]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [h0, h34, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p35_1]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [h6, hlam, p35_0]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [h0, h28, h34, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p35_1]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [h0, h32, h34, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p35_1]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [hlam, p35_0]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          rcases p35_3 (m.d 0 3) (by simp) with h67 | h67
                                          · rcases p35_3 (m.d 1 3) (by simp) with h68 | h68
                                            · linarith only [h12, h68, hlam]
                                            · linarith only [h28, h68, hlam]
                                          · linarith only [h67, h7, hlam]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [h7, hlam, p35_0]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [h28, hlam, p35_0]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [h32, hlam, p35_0]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [h34, hlam, p35_0]
                                        · obtain ⟨p35_0, p35_1, p35_2, p35_3⟩ := h35c
                                          linarith only [hlam, p35_0]
                                      · linarith only [h34, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h30, h32, h33, hc35, hlam, hphi, u5elo4]
                                  · linarith only [h32, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h12, h29, hc13, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h28, h9, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h11, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h83 | h83
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
                          · linarith only [h10, h84, h9, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h86 | h86
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h87 | h87
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                                · linarith only [h10, h84, h88, h9, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h90 | h90
                                  · linarith only [h0, h10, h4, h6, h88, h9, h90, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h90, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h10, h87, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                            · linarith only [h86, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h83, h9, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h96 | h96
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h97 | h97
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h99 | h99
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h100 | h100
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h101 | h101
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h102 | h102
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h103 | h103
                                    · linarith only [h0, h103, h4, h9, h96, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                    · linarith only [h103, hc24, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h101, h102, h9, h96, hc34, hlam, hphi, ht45, u5elo3]
                                · linarith only [h0, h101, h4, h6, h9, h96, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                              · linarith only [h100, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h99, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h9, h96, h98, hlam]
                        · linarith only [h96, h97, hc24, hlam, hphi, ht45, u5elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h112 | h112
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h113 | h113
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h114 | h114
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h115 | h115
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h116 | h116
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h117 | h117
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h118 | h118
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h119 | h119
                                      · rcases h3bigk with h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [hlam, p120_0]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [h0, h113, h119, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p120_1]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [h0, h112, h117, h119, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p120_1]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          rcases p120_3 (m.d 0 3) (by simp) with h124 | h124
                                          · rcases p120_3 (m.d 1 3) (by simp) with h125 | h125
                                            · linarith only [h1, h125, hlam]
                                            · linarith only [h113, h125, hlam]
                                          · linarith only [h124, hlam, p120_0]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          rcases p120_3 (m.d 0 3) (by simp) with h129 | h129
                                          · rcases p120_3 (m.d 1 3) (by simp) with h130 | h130
                                            · linarith only [h1, h130, hlam]
                                            · linarith only [h114, h130, hlam]
                                          · linarith only [h129, hlam, p120_0]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [h1, hlam, p120_0]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [hlam, p120_0]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [h9, hlam, p120_1]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [h1, h119, hc01, hc45, hlam, hphi, ht0b, ht5b, p120_1]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          rcases p120_3 (m.d 0 3) (by simp) with h138 | h138
                                          · rcases p120_3 (m.d 1 3) (by simp) with h139 | h139
                                            · rcases p120_3 (m.d 2 3) (by simp) with h140 | h140
                                              · rcases p120_3 (m.d 3 4) (by simp) with h141 | h141
                                                · linarith only [h113, h141, hlam]
                                                · linarith only [h119, h141, hlam]
                                              · linarith only [h117, h140, hlam]
                                            · linarith only [h139, hlam, p120_0]
                                          · linarith only [h138, h7, hlam]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [h4, hlam, p120_0]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [h0, h112, h117, h119, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p120_1]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [hlam, p120_0]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [h0, h119, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p120_1]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          rcases p120_3 (m.d 0 3) (by simp) with h151 | h151
                                          · rcases p120_3 (m.d 1 3) (by simp) with h152 | h152
                                            · linarith only [h152, h9, hlam]
                                            · linarith only [h114, h152, hlam]
                                          · linarith only [h151, h7, hlam]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [h6, hlam, p120_0]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [h113, hlam, p120_0]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [h116, hlam, p120_0]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [hlam, p120_0]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [h1, h113, h119, hc01, hc45, hlam, hphi, ht0b, ht5b, p120_1]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [h7, hlam, p120_0]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [h114, hlam, p120_0]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [h117, hlam, p120_0]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [h119, hlam, p120_0]
                                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                                          linarith only [hlam, p120_0]
                                      · linarith only [h119, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h112, h115, h118, h96, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h117, h9, hc13, hlam, hphi, ht34, ht45, u5elo3]
                                · linarith only [h112, h116, h6, h9, hc03, hc25, hlam, hphi, ht0b, ht5b]
                              · linarith only [h115, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h114, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h172 | h172
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h173 | h173
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h174 | h174
                                · linarith only [h0, h112, h113, h174, h4, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
                                · linarith only [h0, h112, h174, h4, h6, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
                              · linarith only [h112, h113, h173, h9, hc25, hlam, hphi, u5elo4]
                            · linarith only [h112, h172, h9, hc25, hlam, hphi, u5elo3]
                        · linarith only [h112, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h8, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h7, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h182 | h182
                · rcases m.htr 0 4 5 (by decide) (by decide) with h183 | h183
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h184 | h184
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h185 | h185
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h186 | h186
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h187 | h187
                          · linarith only [h1, h182, h187, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h189 | h189
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h190 | h190
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h191 | h191
                                · linarith only [h1, h184, h189, h191, h6, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h193 | h193
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h194 | h194
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h195 | h195
                                      · rcases h3bigk with h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [hlam, p196_0]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [h184, h193, h195, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p196_1]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [h193, h195, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p196_1]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [h6, hlam, p196_0]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          rcases p196_3 (m.d 0 3) (by simp) with h201 | h201
                                          · rcases p196_3 (m.d 1 3) (by simp) with h202 | h202
                                            · linarith only [h1, h202, hlam]
                                            · linarith only [h189, h202, hlam]
                                          · linarith only [h201, hlam, p196_0]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [h1, hlam, p196_0]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [hlam, p196_0]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [h1, h193, h195, hc01, hc45, hlam, hphi, ht0b, ht5b, p196_1]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [h187, hlam, p196_0]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          rcases p196_3 (m.d 0 3) (by simp) with h210 | h210
                                          · rcases p196_3 (m.d 1 3) (by simp) with h211 | h211
                                            · rcases p196_3 (m.d 2 3) (by simp) with h212 | h212
                                              · linarith only [h184, h212, hlam]
                                              · linarith only [h193, h212, hlam]
                                            · linarith only [h211, hlam, p196_0]
                                          · linarith only [h182, h210, hlam]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [h4, hlam, p196_0]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [h184, hlam, p196_0]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [hlam, p196_0]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [h191, hlam, p196_0]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [h0, h184, h195, hc01, hc45, hlam, hphi, ht0b, ht5b, p196_1]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          rcases p196_3 (m.d 0 3) (by simp) with h222 | h222
                                          · linarith only [h222, hlam, p196_0]
                                          · rcases p196_3 (m.d 1 3) (by simp) with h224 | h224
                                            · linarith only [h187, h224, hlam]
                                            · rcases p196_3 (m.d 2 3) (by simp) with h226 | h226
                                              · linarith only [h191, h226, hlam]
                                              · rcases p196_3 (m.d 3 4) (by simp) with h228 | h228
                                                · rcases p196_3 (m.d 3 5) (by simp) with h229 | h229
                                                  · linarith only [h195, h229, hlam]
                                                  · rcases h4bigk with h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [hlam, p231_0]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h187, h6, hc13, hc34, hlam, hphi, p231_1]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h191, h6, hc23, hc34, hlam, hphi, p231_1]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h6, hlam, p231_0]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      rcases p231_3 (m.d 0 4) (by simp) with h236 | h236
                                                      · rcases p231_3 (m.d 1 4) (by simp) with h237 | h237
                                                        · linarith only [h2, h237, hlam]
                                                        · linarith only [h190, h237, hlam]
                                                      · linarith only [h236, hlam, p231_0]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h2, hlam, p231_0]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [hlam, p231_0]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h191, h193, h195, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p231_1]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h187, hlam, p231_0]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h0, h185, hc01, hc45, hlam, hphi, ht0b, ht5b, p231_1]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h5, hlam, p231_1]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h185, hlam, p231_1]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [hlam, p231_0]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h191, hlam, p231_1]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p231_1]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h6, hc03, hc34, hlam, hphi, p231_1]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h184, h187, h193, h195, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p231_1]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h191, h193, h195, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p231_1]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [hlam, p231_0]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      rcases p231_3 (m.d 0 4) (by simp) with h255 | h255
                                                      · linarith only [h255, h6, hlam]
                                                      · linarith only [h183, h255, hlam]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h183, hlam, p231_0]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h190, hlam, p231_0]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h194, hlam, p231_0]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [h195, hlam, p231_0]
                                                    · obtain ⟨p231_0, p231_1, p231_2, p231_3⟩ := h231c
                                                      linarith only [hlam, p231_0]
                                                · linarith only [h228, hlam, p196_0]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          rcases p196_3 (m.d 0 3) (by simp) with h264 | h264
                                          · linarith only [h264, h6, hlam]
                                          · linarith only [h1, h264, hlam]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          rcases p196_3 (m.d 0 3) (by simp) with h267 | h267
                                          · linarith only [h267, h6, hlam]
                                          · linarith only [h267, h4, hlam]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [hlam, p196_0]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          rcases p196_3 (m.d 0 3) (by simp) with h271 | h271
                                          · linarith only [h271, h6, hlam]
                                          · linarith only [h182, h271, hlam]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [h182, hlam, p196_0]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [h189, hlam, p196_0]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [h193, hlam, p196_0]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [h195, hlam, p196_0]
                                        · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                          linarith only [hlam, p196_0]
                                      · linarith only [h195, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h191, h194, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                  · linarith only [h1, h189, h193, h6, hc23, hc34, hlam, hphi]
                              · linarith only [h187, h190, hc13, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h184, h189, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h186, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h285 | h285
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h286 | h286
                          · linarith only [h1, h286, h6, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h288 | h288
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h289 | h289
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h290 | h290
                                · linarith only [h184, h185, h290, h5, h6, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h292 | h292
                                  · linarith only [h0, h184, h185, h292, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h292, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h185, h289, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                            · linarith only [h184, h288, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h184, h285, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h298 | h298
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h299 | h299
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h300 | h300
                          · linarith only [h184, h300, h4, h6, hlam]
                          · linarith only [h184, h298, h300, hlam]
                        · linarith only [h299, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h304 | h304
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h305 | h305
                          · linarith only [h184, h304, h305, h4, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h307 | h307
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h308 | h308
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h309 | h309
                                · linarith only [h309, h4, h6, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h311 | h311
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h312 | h312
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h313 | h313
                                      · rcases h3bigk with h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [hlam, p314_0]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [h6, hc13, hc34, hlam, hphi, p314_1]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [h184, h304, h311, h313, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p314_1]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [h6, hlam, p314_0]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          rcases p314_3 (m.d 0 3) (by simp) with h319 | h319
                                          · rcases p314_3 (m.d 1 3) (by simp) with h320 | h320
                                            · linarith only [h1, h320, hlam]
                                            · linarith only [h307, h320, hlam]
                                          · linarith only [h319, hlam, p314_0]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [h1, hlam, p314_0]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [hlam, p314_0]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [h184, hlam, p314_1]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [h305, hlam, p314_0]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          rcases p314_3 (m.d 0 3) (by simp) with h328 | h328
                                          · rcases p314_3 (m.d 1 3) (by simp) with h329 | h329
                                            · rcases p314_3 (m.d 2 3) (by simp) with h330 | h330
                                              · rcases p314_3 (m.d 3 4) (by simp) with h331 | h331
                                                · rcases p314_3 (m.d 3 5) (by simp) with h332 | h332
                                                  · linarith only [h332, hlam, p314_0]
                                                  · rcases h4bigk with h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [hlam, p334_0]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h305, h313, hc04, hc45, hlam, hphi, ht0b, ht5b, p314_1, p334_1]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h0, h184, h304, h309, h311, h313, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p334_1]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h6, hlam, p334_0]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      rcases p334_3 (m.d 0 4) (by simp) with h339 | h339
                                                      · rcases p334_3 (m.d 1 4) (by simp) with h340 | h340
                                                        · linarith only [h2, h340, hlam]
                                                        · linarith only [h308, h340, hlam]
                                                      · linarith only [h339, hlam, p334_0]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h2, hlam, p334_0]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [hlam, p334_0]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h298, hlam, p334_0]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h305, hlam, p334_0]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p334_1]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h5, hlam, p334_1]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h0, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p334_1]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [hlam, p334_0]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h309, hlam, p334_1]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p334_1]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h2, h305, h313, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p314_1, p334_1]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h305, h313, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p314_1, p334_1]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h298, h304, h311, h313, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p334_1]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [hlam, p334_0]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      rcases p334_3 (m.d 0 4) (by simp) with h358 | h358
                                                      · linarith only [h358, h6, hlam]
                                                      · linarith only [h183, h358, hlam]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h183, hlam, p334_0]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h308, hlam, p334_0]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h312, hlam, p334_0]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [h313, hlam, p334_0]
                                                    · obtain ⟨p334_0, p334_1, p334_2, p334_3⟩ := h334c
                                                      linarith only [hlam, p334_0]
                                                · linarith only [h313, h331, hlam]
                                              · linarith only [h311, h330, hlam]
                                            · linarith only [h329, hlam, p314_0]
                                          · linarith only [h182, h328, hlam]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [h4, hlam, p314_0]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [h4, h6, hc13, hc34, hlam, hphi, p314_1]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [hlam, p314_0]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [h309, hlam, p314_0]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          rcases p314_3 (m.d 0 3) (by simp) with h374 | h374
                                          · rcases p314_3 (m.d 1 3) (by simp) with h375 | h375
                                            · linarith only [h184, h375, hlam]
                                            · linarith only [h307, h375, hlam]
                                          · linarith only [h182, h374, hlam]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [h184, h304, h311, h313, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p314_1]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          rcases p314_3 (m.d 0 3) (by simp) with h380 | h380
                                          · linarith only [h380, h6, hlam]
                                          · linarith only [h1, h380, hlam]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [h184, h304, h311, h313, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p314_1]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [hlam, p314_0]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [h184, h304, h311, h4, h6, hlam, p314_2]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [h182, hlam, p314_0]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [h307, hlam, p314_0]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [h311, hlam, p314_0]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [h313, hlam, p314_0]
                                        · obtain ⟨p314_0, p314_1, p314_2, p314_3⟩ := h314c
                                          linarith only [hlam, p314_0]
                                      · linarith only [h184, h304, h311, h313, h4, h6, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                    · linarith only [h184, h304, h308, h309, h311, h312, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h184, h304, h311, hc25, hlam, hphi, u5elo3]
                              · linarith only [h308, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h184, h304, h307, hc25, hlam, hphi, u5elo3]
                        · linarith only [h304, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h183, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h182, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h399 | h399
              · linarith only [h399, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h401 | h401
                · rcases m.htr 0 4 5 (by decide) (by decide) with h402 | h402
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h403 | h403
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h404 | h404
                      · linarith only [h0, h404, h5, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h406 | h406
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h407 | h407
                          · linarith only [h1, h399, h401, h407, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h409 | h409
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h410 | h410
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h411 | h411
                                · linarith only [h0, h1, h399, h403, h409, h411, hc02, hc35, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h413 | h413
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h414 | h414
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h415 | h415
                                      · rcases h3bigk with h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [hlam, p416_0]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [h4, h403, h411, h413, h415, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p416_1]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [h4, h411, h413, h415, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p416_1]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [h399, hlam, p416_0]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          rcases p416_3 (m.d 0 3) (by simp) with h421 | h421
                                          · rcases p416_3 (m.d 1 3) (by simp) with h422 | h422
                                            · linarith only [h1, h422, hlam]
                                            · linarith only [h409, h422, hlam]
                                          · linarith only [h421, hlam, p416_0]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [h1, hlam, p416_0]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [hlam, p416_0]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [h1, h413, h415, hc01, hc45, hlam, hphi, ht0b, ht5b, p416_1]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [h407, hlam, p416_0]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          rcases p416_3 (m.d 0 3) (by simp) with h430 | h430
                                          · rcases p416_3 (m.d 1 3) (by simp) with h431 | h431
                                            · rcases p416_3 (m.d 2 3) (by simp) with h432 | h432
                                              · linarith only [h403, h432, hlam]
                                              · linarith only [h413, h432, hlam]
                                            · linarith only [h431, hlam, p416_0]
                                          · linarith only [h401, h430, hlam]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [h4, hlam, p416_0]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [h403, hlam, p416_0]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [hlam, p416_0]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [h411, hlam, p416_0]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [h4, h411, h415, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p416_1]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          rcases p416_3 (m.d 0 3) (by simp) with h442 | h442
                                          · linarith only [h442, hlam, p416_0]
                                          · rcases p416_3 (m.d 1 3) (by simp) with h444 | h444
                                            · linarith only [h407, h444, hlam]
                                            · rcases p416_3 (m.d 2 3) (by simp) with h446 | h446
                                              · linarith only [h411, h446, hlam]
                                              · rcases p416_3 (m.d 3 4) (by simp) with h448 | h448
                                                · rcases p416_3 (m.d 3 5) (by simp) with h449 | h449
                                                  · linarith only [h415, h449, hlam]
                                                  · rcases h4bigk with h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [hlam, p451_0]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [h404, h411, h5, hc12, hc34, hlam, hphi, ht23, p451_1]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [h5, hlam, p451_0]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [h399, hlam, p451_0]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      rcases p451_3 (m.d 0 4) (by simp) with h456 | h456
                                                      · rcases p451_3 (m.d 1 4) (by simp) with h457 | h457
                                                        · linarith only [h2, h457, hlam]
                                                        · linarith only [h410, h457, hlam]
                                                      · linarith only [h456, hlam, p451_0]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [h2, hlam, p451_0]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [hlam, p451_0]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [h404, hlam, p451_0]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [h407, hlam, p451_0]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p451_1]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [h411, h5, hc02, hc34, hlam, hphi, ht23, p451_1]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [h403, h404, h411, h413, h415, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p451_1]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [hlam, p451_0]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [h411, hlam, p451_1]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      rcases p451_3 (m.d 0 4) (by simp) with h470 | h470
                                                      · linarith only [h470, h5, hlam]
                                                      · linarith only [h402, h470, hlam]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [h0, h403, h413, h415, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p451_1]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [h403, h404, h413, h415, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p451_1]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [h0, h403, h413, h415, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p451_1]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [hlam, p451_0]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      rcases p451_3 (m.d 0 4) (by simp) with h477 | h477
                                                      · linarith only [h399, h477, hlam]
                                                      · linarith only [h402, h477, hlam]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [h402, hlam, p451_0]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [h410, hlam, p451_0]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [h414, hlam, p451_0]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [h415, hlam, p451_0]
                                                    · obtain ⟨p451_0, p451_1, p451_2, p451_3⟩ := h451c
                                                      linarith only [hlam, p451_0]
                                                · linarith only [h448, hlam, p416_0]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          rcases p416_3 (m.d 0 3) (by simp) with h486 | h486
                                          · linarith only [h399, h486, hlam]
                                          · linarith only [h1, h486, hlam]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          rcases p416_3 (m.d 0 3) (by simp) with h489 | h489
                                          · linarith only [h399, h489, hlam]
                                          · linarith only [h4, h489, hlam]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [hlam, p416_0]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [h0, h403, h411, h413, h5, hlam, p416_2]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [h401, hlam, p416_0]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [h409, hlam, p416_0]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [h413, hlam, p416_0]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [h415, hlam, p416_0]
                                        · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                          linarith only [hlam, p416_0]
                                      · linarith only [h0, h403, h411, h415, h5, hc23, hc45, hlam, hphi, ht34]
                                    · linarith only [h0, h3, h403, h410, h413, h414, h5, hc35, hlam, hphi, u5elo0]
                                  · linarith only [h413, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h403, h404, h410, hc23, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h409, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h403, h406, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · linarith only [h4, h403, h5, hc12, hc24, hlam, hphi]
                  · linarith only [h402, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h401, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h508 | h508
            · rcases m.htr 0 3 4 (by decide) (by decide) with h509 | h509
              · rcases m.htr 0 3 5 (by decide) (by decide) with h510 | h510
                · rcases m.htr 0 4 5 (by decide) (by decide) with h511 | h511
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h512 | h512
                    · linarith only [h0, h4, h508, h512, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h514 | h514
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h515 | h515
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h516 | h516
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h517 | h517
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h518 | h518
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h519 | h519
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h520 | h520
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h521 | h521
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h522 | h522
                                      · rcases h3bigk with h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [hlam, p523_0]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [h512, h514, h519, h522, hc03, hc45, hlam, hphi, ht0b, ht5b, p523_1]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [h4, hlam, p523_1]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          rcases p523_3 (m.d 0 3) (by simp) with h527 | h527
                                          · rcases p523_3 (m.d 1 3) (by simp) with h528 | h528
                                            · linarith only [h1, h528, hlam]
                                            · linarith only [h516, h528, hlam]
                                          · linarith only [h527, hlam, p523_0]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          rcases p523_3 (m.d 0 3) (by simp) with h532 | h532
                                          · rcases p523_3 (m.d 1 3) (by simp) with h533 | h533
                                            · linarith only [h1, h533, hlam]
                                            · linarith only [h517, h533, hlam]
                                          · linarith only [h532, hlam, p523_0]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [h1, hlam, p523_0]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [hlam, p523_0]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [h512, hlam, p523_1]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [h1, h522, hc01, hc45, hlam, hphi, ht0b, ht5b, p523_1]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          rcases p523_3 (m.d 0 3) (by simp) with h541 | h541
                                          · rcases p523_3 (m.d 1 3) (by simp) with h542 | h542
                                            · rcases p523_3 (m.d 2 3) (by simp) with h543 | h543
                                              · rcases p523_3 (m.d 3 4) (by simp) with h544 | h544
                                                · linarith only [h516, h544, hlam]
                                                · linarith only [h522, h544, hlam]
                                              · linarith only [h520, h543, hlam]
                                            · linarith only [h542, hlam, p523_0]
                                          · linarith only [h510, h541, hlam]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [h0, h4, h514, h519, h522, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p523_1]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [h512, h514, h519, h522, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p523_1]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [hlam, p523_0]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          rcases p523_3 (m.d 0 3) (by simp) with h553 | h553
                                          · linarith only [h4, h553, hlam]
                                          · linarith only [h509, h553, hlam]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          rcases p523_3 (m.d 0 3) (by simp) with h556 | h556
                                          · linarith only [h4, h556, hlam]
                                          · linarith only [h510, h556, hlam]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [h509, hlam, p523_0]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [h516, hlam, p523_0]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [h519, hlam, p523_0]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [hlam, p523_0]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [h0, h514, h519, hc01, hc35, hlam, hphi, ht0b, ht5b, p523_1]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [h510, hlam, p523_0]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [h517, hlam, p523_0]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [h520, hlam, p523_0]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [h522, hlam, p523_0]
                                        · obtain ⟨p523_0, p523_1, p523_2, p523_3⟩ := h523c
                                          linarith only [hlam, p523_0]
                                      · linarith only [h522, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h521, hc24, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h4, h520, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                · linarith only [h4, h509, h519, hlam]
                              · linarith only [h518, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h517, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h512, h514, h516, hlam]
                        · linarith only [h514, h515, hc24, hlam, hphi, ht45, u5elo2]
                      · linarith only [h4, h508, h514, hc12, hc23, hlam, hphi]
                  · linarith only [h511, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h510, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h4, h508, h509, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h581 | h581
              · rcases m.htr 0 3 5 (by decide) (by decide) with h582 | h582
                · rcases m.htr 0 4 5 (by decide) (by decide) with h583 | h583
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h584 | h584
                    · linarith only [h0, h4, h584, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h586 | h586
                      · linarith only [h0, h508, h586, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h588 | h588
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h589 | h589
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h590 | h590
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h591 | h591
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h592 | h592
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h593 | h593
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h594 | h594
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h595 | h595
                                      · rcases h3bigk with h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [hlam, p596_0]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [h589, h595, hc03, hc45, hlam, hphi, ht0b, ht5b, p596_1]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [h4, hlam, p596_1]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          rcases p596_3 (m.d 0 3) (by simp) with h600 | h600
                                          · rcases p596_3 (m.d 1 3) (by simp) with h601 | h601
                                            · linarith only [h1, h601, hlam]
                                            · linarith only [h589, h601, hlam]
                                          · linarith only [h600, hlam, p596_0]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          rcases p596_3 (m.d 0 3) (by simp) with h605 | h605
                                          · rcases p596_3 (m.d 1 3) (by simp) with h606 | h606
                                            · linarith only [h1, h606, hlam]
                                            · linarith only [h590, h606, hlam]
                                          · linarith only [h605, hlam, p596_0]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [h1, hlam, p596_0]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [hlam, p596_0]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [h584, hlam, p596_1]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [h1, h595, hc01, hc45, hlam, hphi, ht0b, ht5b, p596_1]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          rcases p596_3 (m.d 0 3) (by simp) with h614 | h614
                                          · rcases p596_3 (m.d 1 3) (by simp) with h615 | h615
                                            · rcases p596_3 (m.d 2 3) (by simp) with h616 | h616
                                              · rcases p596_3 (m.d 3 4) (by simp) with h617 | h617
                                                · linarith only [h589, h617, hlam]
                                                · linarith only [h595, h617, hlam]
                                              · linarith only [h593, h616, hlam]
                                            · linarith only [h615, hlam, p596_0]
                                          · linarith only [h582, h614, hlam]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [h581, h595, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p596_1]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [h589, h595, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p596_1]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [hlam, p596_0]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          rcases p596_3 (m.d 0 3) (by simp) with h626 | h626
                                          · linarith only [h4, h626, hlam]
                                          · linarith only [h581, h626, hlam]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          rcases p596_3 (m.d 0 3) (by simp) with h629 | h629
                                          · linarith only [h4, h629, hlam]
                                          · linarith only [h582, h629, hlam]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [h581, hlam, p596_0]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [h589, hlam, p596_0]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [h592, hlam, p596_0]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [hlam, p596_0]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [h1, h589, hc01, hc35, hlam, hphi, ht0b, ht5b, p596_1]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [h582, hlam, p596_0]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [h590, hlam, p596_0]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [h593, hlam, p596_0]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [h595, hlam, p596_0]
                                        · obtain ⟨p596_0, p596_1, p596_2, p596_3⟩ := h596c
                                          linarith only [hlam, p596_0]
                                      · linarith only [h595, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h3, h508, h591, h594, hc02, hlam, hphi, ht23, ht34, ht45, u5elo0]
                                  · linarith only [h593, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · linarith only [h0, h2, h4, h588, h589, h592, hc01, hc25, hlam, hphi, ht0b, ht5b]
                              · linarith only [h586, h588, h591, hc25, hlam, hphi, u5elo4]
                            · linarith only [h586, h588, h589, h590, hc25, hlam, hphi, u5elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h648 | h648
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h649 | h649
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h650 | h650
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h651 | h651
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h652 | h652
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h653 | h653
                                      · rcases h3bigk with h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [hlam, p654_0]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          rcases p654_3 (m.d 0 3) (by simp) with h656 | h656
                                          · rcases p654_3 (m.d 1 3) (by simp) with h657 | h657
                                            · linarith only [h1, h657, hlam]
                                            · rcases p654_3 (m.d 2 3) (by simp) with h659 | h659
                                              · rcases p654_3 (m.d 3 4) (by simp) with h660 | h660
                                                · linarith only [h581, h660, hlam]
                                                · linarith only [h589, h660, hlam]
                                              · linarith only [h584, h659, hlam]
                                          · linarith only [h1, h656, hlam]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [h4, hlam, p654_1]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [h584, h588, h589, h651, h653, hc03, hc45, hlam, hphi, ht0b, ht5b, p654_1]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [h581, h584, h588, h589, h651, hlam, p654_2]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [h1, hlam, p654_0]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [hlam, p654_0]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [h584, hlam, p654_1]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [h589, hlam, p654_0]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [h581, h589, h653, hc03, hc45, hlam, hphi, ht0b, ht5b, p654_1]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [h581, h589, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p654_1]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          rcases p654_3 (m.d 0 3) (by simp) with h674 | h674
                                          · linarith only [h4, h674, hlam]
                                          · linarith only [h1, h674, hlam]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [hlam, p654_0]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [h584, h588, h589, h651, h653, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p654_1]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [h4, h581, h584, h588, h589, h651, hlam, p654_2]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [h581, hlam, p654_0]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [h581, h584, h588, h651, h653, hc03, hc45, hlam, hphi, ht0b, ht5b, p654_1]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [h650, hlam, p654_0]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [hlam, p654_0]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          rcases p654_3 (m.d 0 3) (by simp) with h684 | h684
                                          · rcases p654_3 (m.d 1 3) (by simp) with h685 | h685
                                            · linarith only [h589, h685, hlam]
                                            · linarith only [h648, h685, hlam]
                                          · linarith only [h582, h684, hlam]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [h582, hlam, p654_0]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [h648, hlam, p654_0]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [h651, hlam, p654_0]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [h653, hlam, p654_0]
                                        · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                                          linarith only [hlam, p654_0]
                                      · linarith only [h653, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h652, hc24, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h4, h581, h584, h589, h651, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h4, h581, h650, hlam]
                              · linarith only [h649, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h584, h648, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h588, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h583, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h582, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h703 | h703
                · rcases m.htr 0 4 5 (by decide) (by decide) with h704 | h704
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h705 | h705
                    · linarith only [h0, h4, h705, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h707 | h707
                      · linarith only [h0, h508, h707, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h709 | h709
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h710 | h710
                          · linarith only [h0, h1, h4, h581, h709, h710, hc01, hc25, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h712 | h712
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h713 | h713
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h714 | h714
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h715 | h715
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h716 | h716
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h717 | h717
                                      · rcases h3bigk with h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h581, h714, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h4, hlam, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h581, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h581, h714, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h1, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h705, hlam, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h710, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h1, h581, h714, h717, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          rcases p718_3 (m.d 0 3) (by simp) with h729 | h729
                                          · linarith only [h4, h729, hlam]
                                          · rcases p718_3 (m.d 1 3) (by simp) with h731 | h731
                                            · linarith only [h705, h731, hlam]
                                            · rcases p718_3 (m.d 2 3) (by simp) with h733 | h733
                                              · rcases p718_3 (m.d 3 4) (by simp) with h734 | h734
                                                · linarith only [h714, h734, hlam]
                                                · linarith only [h581, h734, hlam]
                                              · linarith only [h4, h733, hlam]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          rcases p718_3 (m.d 0 3) (by simp) with h738 | h738
                                          · linarith only [h4, h738, hlam]
                                          · linarith only [h1, h738, hlam]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h4, h581, hc02, hc23, hlam, hphi, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h0, h4, h581, h709, h714, h715, hlam, p718_2]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h0, h4, h709, h714, h715, h717, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h705, h709, h714, h715, h717, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h714, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          rcases p718_3 (m.d 0 3) (by simp) with h748 | h748
                                          · linarith only [h581, h748, hlam]
                                          · linarith only [h703, h748, hlam]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h703, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h712, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h715, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h717, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [hlam, p718_0]
                                      · linarith only [h717, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h3, h4, h581, h713, h714, h716, hc02, hlam, hphi, ht23, ht34, ht45, u5elo0]
                                  · linarith only [h0, h4, h581, h709, h714, h715, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h759 | h759
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h760 | h760
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h761 | h761
                                      · rcases h3bigk with h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [hlam, p762_0]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [h4, h705, h709, h714, h759, h761, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p762_1]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [h4, hlam, p762_1]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [h581, hlam, p762_0]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          rcases p762_3 (m.d 0 3) (by simp) with h767 | h767
                                          · rcases p762_3 (m.d 1 3) (by simp) with h768 | h768
                                            · linarith only [h1, h768, hlam]
                                            · linarith only [h712, h768, hlam]
                                          · linarith only [h767, hlam, p762_0]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [h1, hlam, p762_0]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [hlam, p762_0]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [h705, hlam, p762_1]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [h710, hlam, p762_0]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          rcases p762_3 (m.d 0 3) (by simp) with h776 | h776
                                          · rcases p762_3 (m.d 1 3) (by simp) with h777 | h777
                                            · rcases p762_3 (m.d 2 3) (by simp) with h778 | h778
                                              · rcases p762_3 (m.d 3 4) (by simp) with h779 | h779
                                                · rcases p762_3 (m.d 3 5) (by simp) with h780 | h780
                                                  · linarith only [h780, hlam, p762_0]
                                                  · rcases h4bigk with h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [hlam, p782_0]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [h710, h761, hc04, hc45, hlam, hphi, ht0b, ht5b, p762_1, p782_1]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [h508, hlam, p782_0]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [h581, hlam, p782_0]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      rcases p782_3 (m.d 0 4) (by simp) with h787 | h787
                                                      · rcases p782_3 (m.d 1 4) (by simp) with h788 | h788
                                                        · linarith only [h2, h788, hlam]
                                                        · linarith only [h713, h788, hlam]
                                                      · linarith only [h787, hlam, p782_0]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [h2, hlam, p782_0]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [hlam, p782_0]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [h707, hlam, p782_0]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [h710, hlam, p782_0]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p782_1]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [h0, h508, h709, h759, h761, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p782_1]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [h707, h709, h759, h761, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p782_1]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [hlam, p782_0]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [h714, hlam, p782_1]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      rcases p782_3 (m.d 0 4) (by simp) with h801 | h801
                                                      · linarith only [h508, h801, hlam]
                                                      · linarith only [h704, h801, hlam]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [h1, h581, h761, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p762_1, p782_1]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [h710, h761, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p762_1, p782_1]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [h0, h508, h709, h759, h761, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p782_1]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [hlam, p782_0]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      rcases p782_3 (m.d 0 4) (by simp) with h808 | h808
                                                      · linarith only [h581, h808, hlam]
                                                      · linarith only [h704, h808, hlam]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [h704, hlam, p782_0]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [h713, hlam, p782_0]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [h760, hlam, p782_0]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [h761, hlam, p782_0]
                                                    · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                                      linarith only [hlam, p782_0]
                                                · linarith only [h761, h779, hlam]
                                              · linarith only [h759, h778, hlam]
                                            · linarith only [h777, hlam, p762_0]
                                          · linarith only [h703, h776, hlam]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [h714, hc03, hc34, hlam, hphi, p762_1]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [h714, hc13, hc34, hlam, hphi, p762_1]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [hlam, p762_0]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [h714, hlam, p762_0]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          rcases p762_3 (m.d 0 3) (by simp) with h824 | h824
                                          · linarith only [h4, h824, hlam]
                                          · linarith only [h703, h824, hlam]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          rcases p762_3 (m.d 0 3) (by simp) with h827 | h827
                                          · linarith only [h827, hlam, p762_0]
                                          · rcases p762_3 (m.d 1 3) (by simp) with h829 | h829
                                            · linarith only [h710, h829, hlam]
                                            · rcases p762_3 (m.d 2 3) (by simp) with h831 | h831
                                              · linarith only [h714, h831, hlam]
                                              · linarith only [h4, h831, hlam]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          rcases p762_3 (m.d 0 3) (by simp) with h834 | h834
                                          · linarith only [h581, h834, hlam]
                                          · linarith only [h1, h834, hlam]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [h0, h4, h709, h759, h761, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p762_1]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [hlam, p762_0]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [h0, h4, h709, h714, h759, hlam, p762_2]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [h703, hlam, p762_0]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [h712, hlam, p762_0]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [h759, hlam, p762_0]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [h761, hlam, p762_0]
                                        · obtain ⟨p762_0, p762_1, p762_2, p762_3⟩ := h762c
                                          linarith only [hlam, p762_0]
                                      · linarith only [h0, h4, h709, h714, h759, h761, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                    · linarith only [h760, hc24, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h4, h759, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                              · linarith only [h713, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h705, h709, h712, hc25, hlam, hphi, u5elo3]
                        · linarith only [h709, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h704, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h703, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h854 | h854
        · rcases m.htr 0 2 3 (by decide) (by decide) with h855 | h855
          · rcases m.htr 0 2 4 (by decide) (by decide) with h856 | h856
            · linarith only [h0, h2, h856, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h858 | h858
              · linarith only [h1, h2, h858, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h860 | h860
                · rcases m.htr 0 4 5 (by decide) (by decide) with h861 | h861
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h862 | h862
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h863 | h863
                      · linarith only [h0, h2, h856, h863, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h865 | h865
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h866 | h866
                          · linarith only [h1, h2, h858, h866, hlam]
                          · linarith only [h0, h2, h862, h866, hc23, hc34, hlam, hphi]
                        · linarith only [h862, h865, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · linarith only [h855, h856, h862, hc12, hc24, hlam, hphi]
                  · linarith only [h2, h861, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h860, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h873 | h873
            · linarith only [h1, h2, h855, h873, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h875 | h875
              · linarith only [h1, h2, h875, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h877 | h877
                · rcases m.htr 0 4 5 (by decide) (by decide) with h878 | h878
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h879 | h879
                    · linarith only [h0, h2, h855, h879, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h881 | h881
                      · linarith only [h0, h2, h873, h881, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h883 | h883
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h884 | h884
                          · linarith only [h1, h2, h855, h875, h881, h884, hc02, hc24, hlam, hphi]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h886 | h886
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h887 | h887
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h888 | h888
                                · linarith only [h0, h2, h883, h884, h888, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h890 | h890
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h891 | h891
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h892 | h892
                                      · rcases h3bigk with h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [hlam, p893_0]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [h1, h2, h879, h883, h890, h892, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p893_1]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [h855, hlam, p893_1]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [h875, hlam, p893_0]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          rcases p893_3 (m.d 0 3) (by simp) with h898 | h898
                                          · rcases p893_3 (m.d 1 3) (by simp) with h899 | h899
                                            · linarith only [h1, h899, hlam]
                                            · linarith only [h886, h899, hlam]
                                          · linarith only [h898, hlam, p893_0]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [h1, hlam, p893_0]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [hlam, p893_0]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [h879, hlam, p893_1]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [h884, hlam, p893_0]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [h1, h2, h881, h888, h892, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p893_1]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [h888, hc03, hc34, hlam, hphi, p893_1]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [h888, hc13, hc34, hlam, hphi, p893_1]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [hlam, p893_0]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [h888, hlam, p893_0]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          rcases p893_3 (m.d 0 3) (by simp) with h912 | h912
                                          · linarith only [h855, h912, hlam]
                                          · linarith only [h877, h912, hlam]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          rcases p893_3 (m.d 0 3) (by simp) with h915 | h915
                                          · linarith only [h915, hlam, p893_0]
                                          · rcases p893_3 (m.d 1 3) (by simp) with h917 | h917
                                            · linarith only [h884, h917, hlam]
                                            · rcases p893_3 (m.d 2 3) (by simp) with h919 | h919
                                              · linarith only [h888, h919, hlam]
                                              · linarith only [h855, h919, hlam]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          rcases p893_3 (m.d 0 3) (by simp) with h922 | h922
                                          · linarith only [h875, h922, hlam]
                                          · linarith only [h1, h922, hlam]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [h0, h855, h883, h890, h892, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p893_1]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [hlam, p893_0]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [h0, h2, h881, h883, h888, h890, hlam, p893_2]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [h877, hlam, p893_0]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [h886, hlam, p893_0]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [h890, hlam, p893_0]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [h892, hlam, p893_0]
                                        · obtain ⟨p893_0, p893_1, p893_2, p893_3⟩ := h893c
                                          linarith only [hlam, p893_0]
                                      · linarith only [h1, h2, h879, h881, h883, h888, h890, h892, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                    · linarith only [h1, h2, h854, h879, h881, h883, h887, h890, h891, hc35, hlam, hphi, u5elo0]
                                  · linarith only [h855, h890, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                              · linarith only [h1, h2, h879, h883, h887, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h879, h883, h886, hc25, hlam, hphi, u5elo3]
                        · linarith only [h883, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h2, h878, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h877, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · linarith only [h0, h854, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h942 | h942
      · rcases m.htr 0 1 5 (by decide) (by decide) with h943 | h943
        · rcases m.htr 0 2 3 (by decide) (by decide) with h944 | h944
          · linarith only [h0, h1, h944, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h946 | h946
            · rcases m.htr 0 3 4 (by decide) (by decide) with h947 | h947
              · rcases m.htr 0 3 5 (by decide) (by decide) with h948 | h948
                · rcases m.htr 0 4 5 (by decide) (by decide) with h949 | h949
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h950 | h950
                    · linarith only [h0, h1, h944, h950, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h952 | h952
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h953 | h953
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h954 | h954
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h955 | h955
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h956 | h956
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h957 | h957
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h958 | h958
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h959 | h959
                                    · linarith only [h0, h1, h950, h952, h959, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                    · linarith only [h959, hc24, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h0, h1, h950, h958, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h950, h952, h956, h957, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h956, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h1, h952, h955, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h952, h954, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h952, h953, hc24, hlam, hphi, ht45, u5elo2]
                      · linarith only [h0, h1, h946, h950, h952, hc12, hc23, hlam, hphi]
                  · linarith only [h949, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h1, h948, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h1, h942, h947, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h972 | h972
              · rcases m.htr 0 3 5 (by decide) (by decide) with h973 | h973
                · rcases m.htr 0 4 5 (by decide) (by decide) with h974 | h974
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h975 | h975
                    · linarith only [h0, h944, h975, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h977 | h977
                      · linarith only [h0, h946, h977, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h979 | h979
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h980 | h980
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h981 | h981
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h982 | h982
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h983 | h983
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h984 | h984
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h985 | h985
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h986 | h986
                                      · rcases h3bigk with h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [hlam, p987_0]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [h1, hlam, p987_1]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [h944, hlam, p987_1]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          rcases p987_3 (m.d 0 3) (by simp) with h991 | h991
                                          · rcases p987_3 (m.d 1 3) (by simp) with h992 | h992
                                            · rcases p987_3 (m.d 2 3) (by simp) with h993 | h993
                                              · rcases p987_3 (m.d 3 4) (by simp) with h994 | h994
                                                · linarith only [h994, hlam, p987_0]
                                                · rcases p987_3 (m.d 3 5) (by simp) with h996 | h996
                                                  · linarith only [h973, h996, hlam]
                                                  · rcases h4bigk with h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [hlam, p998_0]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h1, h942, h975, h977, h979, h984, h986, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p998_1]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h946, hlam, p998_0]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h1, h942, h975, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p998_1]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h1, h942, h975, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p998_1]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h942, hlam, p998_0]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [hlam, p998_0]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h977, hlam, p998_0]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h1, h942, h975, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p998_1]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h1, h942, h975, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p998_1]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h0, h946, h979, h984, h986, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p998_1]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h977, h979, h984, h986, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p998_1]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [hlam, p998_0]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h983, h986, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p998_1]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      rcases p998_3 (m.d 0 4) (by simp) with h1013 | h1013
                                                      · linarith only [h1013, h946, hlam]
                                                      · linarith only [h1013, h974, hlam]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h972, hlam, p998_1]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h980, hlam, p998_1]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h983, hlam, p998_0]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [hlam, p998_0]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [hc03, hc45, hlam, hphi, ht0b, ht5b, p987_1, p998_1]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h974, hlam, p998_0]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h982, hlam, p998_0]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h985, hlam, p998_0]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [h986, hlam, p998_0]
                                                    · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                                      linarith only [hlam, p998_0]
                                              · linarith only [h983, h993, hlam]
                                            · linarith only [h980, h992, hlam]
                                          · linarith only [h991, hlam, p987_0]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          rcases p987_3 (m.d 0 3) (by simp) with h1029 | h1029
                                          · rcases p987_3 (m.d 1 3) (by simp) with h1030 | h1030
                                            · rcases p987_3 (m.d 2 3) (by simp) with h1031 | h1031
                                              · rcases p987_3 (m.d 3 4) (by simp) with h1032 | h1032
                                                · linarith only [h1032, h972, hlam]
                                                · linarith only [h1032, h986, hlam]
                                              · linarith only [h1031, h984, hlam]
                                            · linarith only [h1030, h981, hlam]
                                          · linarith only [h1029, hlam, p987_0]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [h0, h1, h975, h979, h984, h986, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p987_1]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [hlam, p987_0]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [h975, hlam, p987_1]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          rcases p987_3 (m.d 0 3) (by simp) with h1041 | h1041
                                          · linarith only [h1, h1041, hlam]
                                          · linarith only [h1041, h972, hlam]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [h1, h942, h977, h979, h984, hlam, p987_2]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [h1, h942, h977, h979, h984, h986, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p987_1]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [h1, h942, h977, h979, h984, h986, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p987_1]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [hlam, p987_0]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          rcases p987_3 (m.d 0 3) (by simp) with h1048 | h1048
                                          · linarith only [h1048, h944, hlam]
                                          · linarith only [h1048, h972, hlam]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [h1, h942, h975, h977, h979, h984, hlam, p987_2]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [h972, hlam, p987_0]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [h980, hlam, p987_0]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [h983, hlam, p987_0]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [hlam, p987_0]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [h1, h942, h980, h986, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p987_1]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [h973, hlam, p987_0]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [h981, hlam, p987_0]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [h984, hlam, p987_0]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [h986, hlam, p987_0]
                                        · obtain ⟨p987_0, p987_1, p987_2, p987_3⟩ := h987c
                                          linarith only [hlam, p987_0]
                                      · linarith only [h986, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h1, h942, h975, h982, h985, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h1, h942, h975, h977, h984, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h1, h942, h975, h977, h979, h983, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h977, h979, h982, hc25, hlam, hphi, u5elo4]
                            · linarith only [h1, h942, h977, h979, h981, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1, h942, h977, h979, h980, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h979, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h974, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h0, h1, h973, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h1, h942, h972, hlam]
        · linarith only [h0, h943, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1074 | h1074
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1075 | h1075
          · linarith only [h0, h1, h1075, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1077 | h1077
            · linarith only [h0, h1077, h942, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1079 | h1079
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1080 | h1080
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1081 | h1081
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1082 | h1082
                    · linarith only [h0, h1, h1075, h1082, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1084 | h1084
                      · linarith only [h0, h1077, h1084, h942, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1086 | h1086
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1087 | h1087
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1088 | h1088
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1089 | h1089
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1090 | h1090
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1091 | h1091
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1092 | h1092
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1093 | h1093
                                      · rcases h3bigk with h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [hlam, p1094_0]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [h1, hlam, p1094_1]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [h1075, hlam, p1094_1]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          rcases p1094_3 (m.d 0 3) (by simp) with h1098 | h1098
                                          · rcases p1094_3 (m.d 1 3) (by simp) with h1099 | h1099
                                            · rcases p1094_3 (m.d 2 3) (by simp) with h1100 | h1100
                                              · rcases p1094_3 (m.d 3 4) (by simp) with h1101 | h1101
                                                · linarith only [h1101, hlam, p1094_0]
                                                · rcases p1094_3 (m.d 3 5) (by simp) with h1103 | h1103
                                                  · linarith only [h1080, h1103, hlam]
                                                  · rcases h4bigk with h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [hlam, p1105_0]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [h942, hlam, p1105_1]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [h1077, hlam, p1105_0]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [h1093, hc04, hc45, hlam, hphi, ht0b, ht5b, p1105_1]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      rcases p1105_3 (m.d 0 4) (by simp) with h1110 | h1110
                                                      · rcases p1105_3 (m.d 1 4) (by simp) with h1111 | h1111
                                                        · rcases p1105_3 (m.d 2 4) (by simp) with h1112 | h1112
                                                          · rcases p1105_3 (m.d 3 4) (by simp) with h1113 | h1113
                                                            · linarith only [h1079, h1113, hlam]
                                                            · linarith only [h1093, h1113, hlam]
                                                          · linarith only [h1092, h1112, hlam]
                                                        · linarith only [h1089, h1111, hlam]
                                                      · linarith only [h1110, hlam, p1105_0]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [h1082, h1087, h942, hc01, hc23, hlam, hphi, ht12, p1105_1]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [hlam, p1105_0]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [h1084, hlam, p1105_0]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [h1082, h1087, h1093, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1105_1]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      rcases p1105_3 (m.d 0 4) (by simp) with h1123 | h1123
                                                      · linarith only [h1123, h942, hlam]
                                                      · linarith only [h1081, h1123, hlam]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [h0, h1086, h1091, h1093, h942, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1105_1]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [h0, h1086, h1091, h1093, h942, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1105_1]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [hlam, p1105_0]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [h1090, h1093, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1105_1]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      rcases p1105_3 (m.d 0 4) (by simp) with h1130 | h1130
                                                      · linarith only [h1077, h1130, hlam]
                                                      · linarith only [h1081, h1130, hlam]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [h1079, hlam, p1105_1]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [h1087, hlam, p1105_1]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [h1090, hlam, p1105_0]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [hlam, p1105_0]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [hc03, hc45, hlam, hphi, ht0b, ht5b, p1094_1, p1105_1]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [h1081, hlam, p1105_0]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [h1089, hlam, p1105_0]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [h1092, hlam, p1105_0]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [h1093, hlam, p1105_0]
                                                    · obtain ⟨p1105_0, p1105_1, p1105_2, p1105_3⟩ := h1105c
                                                      linarith only [hlam, p1105_0]
                                              · linarith only [h1090, h1100, hlam]
                                            · linarith only [h1087, h1099, hlam]
                                          · linarith only [h1098, hlam, p1094_0]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          rcases p1094_3 (m.d 0 3) (by simp) with h1146 | h1146
                                          · rcases p1094_3 (m.d 1 3) (by simp) with h1147 | h1147
                                            · rcases p1094_3 (m.d 2 3) (by simp) with h1148 | h1148
                                              · rcases p1094_3 (m.d 3 4) (by simp) with h1149 | h1149
                                                · linarith only [h1079, h1149, hlam]
                                                · linarith only [h1093, h1149, hlam]
                                              · linarith only [h1091, h1148, hlam]
                                            · linarith only [h1088, h1147, hlam]
                                          · linarith only [h1146, hlam, p1094_0]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [h0, h1, h1082, h1086, h1091, h1093, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1094_1]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [hlam, p1094_0]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [h1082, hlam, p1094_1]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          rcases p1094_3 (m.d 0 3) (by simp) with h1158 | h1158
                                          · linarith only [h1, h1158, hlam]
                                          · linarith only [h1079, h1158, hlam]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [h0, h1, h1086, h1091, hlam, p1094_2]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [h0, h1079, h1086, h1091, h1093, h942, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1094_1]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [h0, h1, h1086, h1091, h1093, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1094_1]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [hlam, p1094_0]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          rcases p1094_3 (m.d 0 3) (by simp) with h1165 | h1165
                                          · linarith only [h1075, h1165, hlam]
                                          · linarith only [h1079, h1165, hlam]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [h0, h1082, h1086, h1087, h1091, h942, hlam, p1094_2]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [h1079, hlam, p1094_0]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [h1087, hlam, p1094_0]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [h1090, hlam, p1094_0]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [hlam, p1094_0]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          rcases p1094_3 (m.d 0 3) (by simp) with h1173 | h1173
                                          · rcases p1094_3 (m.d 1 3) (by simp) with h1174 | h1174
                                            · rcases p1094_3 (m.d 2 3) (by simp) with h1175 | h1175
                                              · rcases p1094_3 (m.d 3 4) (by simp) with h1176 | h1176
                                                · rcases p1094_3 (m.d 3 5) (by simp) with h1177 | h1177
                                                  · linarith only [h1093, h1177, hlam]
                                                  · rcases h4bigk with h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [hlam, p1179_0]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [h942, hlam, p1179_1]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [h1077, hlam, p1179_0]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [h1093, hc04, hc45, hlam, hphi, ht0b, ht5b, p1094_1, p1179_1]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      rcases p1179_3 (m.d 0 4) (by simp) with h1184 | h1184
                                                      · rcases p1179_3 (m.d 1 4) (by simp) with h1185 | h1185
                                                        · rcases p1179_3 (m.d 2 4) (by simp) with h1186 | h1186
                                                          · rcases p1179_3 (m.d 3 4) (by simp) with h1187 | h1187
                                                            · linarith only [h1079, h1187, hlam]
                                                            · linarith only [h1093, h1187, hlam]
                                                          · linarith only [h1092, h1186, hlam]
                                                        · linarith only [h1089, h1185, hlam]
                                                      · linarith only [h1184, hlam, p1179_0]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [h0, h1086, h1087, h1091, h1093, h942, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1179_1]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [hlam, p1179_0]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [h1084, hlam, p1179_0]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [h1082, h1087, h1093, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1094_1, p1179_1]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      rcases p1179_3 (m.d 0 4) (by simp) with h1197 | h1197
                                                      · linarith only [h1197, h942, hlam]
                                                      · linarith only [h1081, h1197, hlam]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [h0, h1086, h1090, h1091, h1093, h942, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1179_1]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [h0, h1086, h1090, h1091, h1093, h942, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1179_1]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [hlam, p1179_0]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [h1090, h1093, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1094_1, p1179_1]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      rcases p1179_3 (m.d 0 4) (by simp) with h1204 | h1204
                                                      · linarith only [h1077, h1204, hlam]
                                                      · linarith only [h1081, h1204, hlam]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [h1079, hlam, p1179_1]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [h1087, hlam, p1179_1]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [h1090, hlam, p1179_0]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [hlam, p1179_0]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [h1079, hc03, hc45, hlam, hphi, ht0b, ht5b, p1179_1]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [h1081, hlam, p1179_0]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [h1089, hlam, p1179_0]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [h1092, hlam, p1179_0]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [h1093, hlam, p1179_0]
                                                    · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                      linarith only [hlam, p1179_0]
                                                · linarith only [h1093, h1176, hlam]
                                              · linarith only [h1091, h1175, hlam]
                                            · linarith only [h1088, h1174, hlam]
                                          · linarith only [h1080, h1173, hlam]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [h1080, hlam, p1094_0]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [h1088, hlam, p1094_0]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [h1091, hlam, p1094_0]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [h1093, hlam, p1094_0]
                                        · obtain ⟨p1094_0, p1094_1, p1094_2, p1094_3⟩ := h1094c
                                          linarith only [hlam, p1094_0]
                                      · linarith only [h1093, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h1074, h1084, h1089, h1092, h942, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                                  · linarith only [h0, h1084, h1086, h1090, h1091, h942, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h0, h1, h1082, h1086, h1090, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h0, h1086, h1089, h942, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h0, h1086, h1087, h1088, h942, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h1, h1086, h1087, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1086, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h1081, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h1080, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1236 | h1236
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1237 | h1237
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1238 | h1238
                    · linarith only [h0, h1, h1079, h1238, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1240 | h1240
                      · linarith only [h0, h1077, h1240, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1242 | h1242
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1243 | h1243
                          · linarith only [h0, h1, h1079, h1238, h1243, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h1242, h1243, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1242, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h1, h1079, h1237, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h0, h1, h1236, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h0, h1074, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1250 | h1250
    · rcases m.htr 0 1 4 (by decide) (by decide) with h1251 | h1251
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1252 | h1252
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1253 | h1253
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1254 | h1254
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1255 | h1255
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1256 | h1256
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1257 | h1257
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1258 | h1258
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1259 | h1259
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1260 | h1260
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1261 | h1261
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1262 | h1262
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1263 | h1263
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1264 | h1264
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1265 | h1265
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1266 | h1266
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1267 | h1267
                                      · linarith only [h0, h1250, h1258, h1264, h1267, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                      · linarith only [h1267, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h0, h1250, h1261, h1263, h1266, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h1265, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · linarith only [h0, h1250, h1261, h1264, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h1263, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h1262, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1275 | h1275
                            · linarith only [h0, h1250, h1255, h1261, h1275, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h1275, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h1260, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h1250, h1254, h1258, h1259, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h1253, h1258, hlam]
                  · linarith only [h1257, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h1255, h1256, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1283 | h1283
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1284 | h1284
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1285 | h1285
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1286 | h1286
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1287 | h1287
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1288 | h1288
                          · linarith only [h1250, h1255, h1283, h1288, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1290 | h1290
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1291 | h1291
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1292 | h1292
                                · linarith only [h1250, h1255, h1285, h1292, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1294 | h1294
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1295 | h1295
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1296 | h1296
                                      · rcases h3bigk with h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [hlam, p1297_0]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [h1255, h1285, h1294, h1296, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1297_1]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [h0, h1251, h1255, h1294, h1296, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1297_1]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [h1255, hlam, p1297_0]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          rcases p1297_3 (m.d 0 3) (by simp) with h1302 | h1302
                                          · rcases p1297_3 (m.d 1 3) (by simp) with h1303 | h1303
                                            · linarith only [h1250, h1303, hlam]
                                            · linarith only [h1290, h1303, hlam]
                                          · linarith only [h1302, hlam, p1297_0]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [h1250, hlam, p1297_0]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [hlam, p1297_0]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [h0, h1250, h1294, h1296, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1297_1]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [h1288, hlam, p1297_0]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [h0, h1251, h1288, h1296, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1297_1]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [h1253, hlam, p1297_0]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [h1285, hlam, p1297_0]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [hlam, p1297_0]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [h1292, hlam, p1297_0]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [h0, h1251, h1285, h1288, h1296, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1297_1]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          rcases p1297_3 (m.d 0 3) (by simp) with h1317 | h1317
                                          · linarith only [h1317, hlam, p1297_0]
                                          · rcases p1297_3 (m.d 1 3) (by simp) with h1319 | h1319
                                            · linarith only [h1288, h1319, hlam]
                                            · rcases p1297_3 (m.d 2 3) (by simp) with h1321 | h1321
                                              · linarith only [h1292, h1321, hlam]
                                              · rcases p1297_3 (m.d 3 4) (by simp) with h1323 | h1323
                                                · rcases p1297_3 (m.d 3 5) (by simp) with h1324 | h1324
                                                  · linarith only [h1296, h1324, hlam]
                                                  · rcases h4bigk with h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [hlam, p1326_0]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h0, h1251, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1326_1]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h0, h1251, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1326_1]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h1255, hlam, p1326_0]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h0, h1251, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1326_1]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h1251, hlam, p1326_0]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [hlam, p1326_0]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h0, h1251, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1326_1]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h1288, hlam, p1326_0]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h0, h1251, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1326_1]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h1254, hlam, p1326_1]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h1286, hlam, p1326_1]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [hlam, p1326_0]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h1292, hlam, p1326_1]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h1254, hc02, hc45, hlam, hphi, ht0b, ht5b, p1326_1]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h1255, hc03, hc34, hlam, hphi, p1326_1]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h1285, h1288, hc23, hc34, hlam, hphi, p1326_1]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h1292, hc23, hc34, hlam, hphi, p1326_1]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [hlam, p1326_0]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      rcases p1326_3 (m.d 0 4) (by simp) with h1346 | h1346
                                                      · linarith only [h1255, h1346, hlam]
                                                      · linarith only [h1284, h1346, hlam]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h1284, hlam, p1326_0]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h1291, hlam, p1326_0]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h1295, hlam, p1326_0]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [h1296, hlam, p1326_0]
                                                    · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                                                      linarith only [hlam, p1326_0]
                                                · linarith only [h1323, hlam, p1297_0]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          rcases p1297_3 (m.d 0 3) (by simp) with h1355 | h1355
                                          · linarith only [h1255, h1355, hlam]
                                          · linarith only [h1250, h1355, hlam]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          rcases p1297_3 (m.d 0 3) (by simp) with h1358 | h1358
                                          · linarith only [h1255, h1358, hlam]
                                          · linarith only [h1253, h1358, hlam]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [hlam, p1297_0]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          rcases p1297_3 (m.d 0 3) (by simp) with h1362 | h1362
                                          · linarith only [h1255, h1362, hlam]
                                          · linarith only [h1283, h1362, hlam]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [h1283, hlam, p1297_0]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [h1290, hlam, p1297_0]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [h1294, hlam, p1297_0]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [h1296, hlam, p1297_0]
                                        · obtain ⟨p1297_0, p1297_1, p1297_2, p1297_3⟩ := h1297c
                                          linarith only [hlam, p1297_0]
                                      · linarith only [h1296, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h1292, h1295, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                  · linarith only [h1250, h1255, h1290, h1294, hc23, hc34, hlam, hphi]
                              · linarith only [h1288, h1291, hc13, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h1255, h1283, h1285, h1290, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h1287, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h1254, h1286, hlam]
                    · linarith only [h0, h1253, h1285, hlam]
                  · linarith only [h1255, h1284, hc03, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h1253, h1283, hc23, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h0, h1251, h1254, hlam]
          · linarith only [h0, h1250, h1253, hlam]
        · linarith only [h1250, h1252, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1383 | h1383
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1384 | h1384
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1385 | h1385
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1386 | h1386
              · linarith only [h1250, h1251, h1386, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1388 | h1388
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1389 | h1389
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1390 | h1390
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1391 | h1391
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1392 | h1392
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1393 | h1393
                          · linarith only [h1250, h1251, h1386, h1391, h1393, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1395 | h1395
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1396 | h1396
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1397 | h1397
                                · linarith only [h1250, h1251, h1390, h1393, h1397, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1399 | h1399
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1400 | h1400
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1401 | h1401
                                      · rcases h3bigk with h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [hlam, p1402_0]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [h1250, h1251, h1390, h1393, h1399, h1401, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1402_1]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [h1250, h1251, h1393, h1399, h1401, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1402_1]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [h1386, hlam, p1402_0]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          rcases p1402_3 (m.d 0 3) (by simp) with h1407 | h1407
                                          · rcases p1402_3 (m.d 1 3) (by simp) with h1408 | h1408
                                            · linarith only [h1250, h1408, hlam]
                                            · linarith only [h1395, h1408, hlam]
                                          · linarith only [h1407, hlam, p1402_0]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [h1250, hlam, p1402_0]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [hlam, p1402_0]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [h1250, h1251, h1393, h1399, h1401, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1402_1]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [h1393, hlam, p1402_0]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [h1250, h1251, h1393, h1401, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1402_1]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [h1384, hlam, p1402_0]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [h1390, hlam, p1402_0]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [hlam, p1402_0]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [h1397, hlam, p1402_0]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [h1250, h1251, h1390, h1393, h1401, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1402_1]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          rcases p1402_3 (m.d 0 3) (by simp) with h1422 | h1422
                                          · linarith only [h1422, hlam, p1402_0]
                                          · rcases p1402_3 (m.d 1 3) (by simp) with h1424 | h1424
                                            · linarith only [h1393, h1424, hlam]
                                            · rcases p1402_3 (m.d 2 3) (by simp) with h1426 | h1426
                                              · linarith only [h1397, h1426, hlam]
                                              · rcases p1402_3 (m.d 3 4) (by simp) with h1428 | h1428
                                                · rcases p1402_3 (m.d 3 5) (by simp) with h1429 | h1429
                                                  · linarith only [h1401, h1429, hlam]
                                                  · rcases h4bigk with h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [hlam, p1431_0]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [h1251, hlam, p1431_1]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [h1251, h1393, h1397, hc23, hc34, hlam, hphi, p1431_1]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [h1386, hlam, p1431_0]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      rcases p1431_3 (m.d 0 4) (by simp) with h1436 | h1436
                                                      · rcases p1431_3 (m.d 1 4) (by simp) with h1437 | h1437
                                                        · rcases p1431_3 (m.d 2 4) (by simp) with h1438 | h1438
                                                          · linarith only [h1385, h1438, hlam]
                                                          · linarith only [h1400, h1438, hlam]
                                                        · linarith only [h1396, h1437, hlam]
                                                      · linarith only [h1436, hlam, p1431_0]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [h1251, h1393, hc01, hc34, hlam, hphi, ht12, ht23, p1431_1]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [hlam, p1431_0]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [h1393, h1397, h1399, h1401, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1431_1]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [h1393, hlam, p1431_0]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      rcases p1431_3 (m.d 0 4) (by simp) with h1447 | h1447
                                                      · linarith only [h1251, h1447, hlam]
                                                      · linarith only [h1389, h1447, hlam]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [h1385, hlam, p1431_1]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [h1391, hlam, p1431_1]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [hlam, p1431_0]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [h1397, hlam, p1431_1]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [h1385, hc02, hc45, hlam, hphi, ht0b, ht5b, p1431_1]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [h1250, h1251, h1390, h1399, h1401, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1431_1]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [h1250, h1251, h1390, h1399, h1401, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1431_1]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [h1397, h1399, h1401, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1431_1]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [hlam, p1431_0]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      rcases p1431_3 (m.d 0 4) (by simp) with h1459 | h1459
                                                      · linarith only [h1386, h1459, hlam]
                                                      · linarith only [h1389, h1459, hlam]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [h1389, hlam, p1431_0]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [h1396, hlam, p1431_0]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [h1400, hlam, p1431_0]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [h1401, hlam, p1431_0]
                                                    · obtain ⟨p1431_0, p1431_1, p1431_2, p1431_3⟩ := h1431c
                                                      linarith only [hlam, p1431_0]
                                                · linarith only [h1428, hlam, p1402_0]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          rcases p1402_3 (m.d 0 3) (by simp) with h1468 | h1468
                                          · linarith only [h1386, h1468, hlam]
                                          · linarith only [h1250, h1468, hlam]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          rcases p1402_3 (m.d 0 3) (by simp) with h1471 | h1471
                                          · linarith only [h1386, h1471, hlam]
                                          · linarith only [h1384, h1471, hlam]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [hlam, p1402_0]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [h1250, h1251, h1390, h1393, h1399, hlam, p1402_2]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [h1388, hlam, p1402_0]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [h1395, hlam, p1402_0]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [h1399, hlam, p1402_0]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [h1401, hlam, p1402_0]
                                        · obtain ⟨p1402_0, p1402_1, p1402_2, p1402_3⟩ := h1402c
                                          linarith only [hlam, p1402_0]
                                      · linarith only [h1250, h1251, h1393, h1401, hc13, hc45, hlam, hphi, ht34]
                                    · linarith only [h1383, h1396, h1397, h1399, h1400, hc35, hlam, hphi, u5elo0]
                                  · linarith only [h1399, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h1250, h1251, h1396, hc13, hc45, hlam, hphi, ht34]
                            · linarith only [h1390, h1395, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h1392, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h1250, h1385, h1390, h1391, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h1384, h1390, hlam]
                  · linarith only [h1251, h1389, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h1388, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1491 | h1491
              · linarith only [h0, h1250, h1385, h1491, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1493 | h1493
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1494 | h1494
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1495 | h1495
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1496 | h1496
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1497 | h1497
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1498 | h1498
                          · linarith only [h0, h1250, h1385, h1496, h1498, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1500 | h1500
                            · linarith only [h0, h1250, h1385, h1496, h1500, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h1500, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h1385, h1496, h1497, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1504 | h1504
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1505 | h1505
                          · linarith only [h0, h1250, h1496, h1505, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1507 | h1507
                            · linarith only [h0, h1250, h1496, h1507, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h1507, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h1504, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h1250, h1384, h1495, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h1494, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h1493, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h0, h1250, h1384, hlam]
        · linarith only [h1383, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h1516 | h1516
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1517 | h1517
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1518 | h1518
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1519 | h1519
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1520 | h1520
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1521 | h1521
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1522 | h1522
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1523 | h1523
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1524 | h1524
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1525 | h1525
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1526 | h1526
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1527 | h1527
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1528 | h1528
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1529 | h1529
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1530 | h1530
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1531 | h1531
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1532 | h1532
                                      · rcases h3bigk with h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [hlam, p1533_0]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [h1250, hlam, p1533_1]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [h1529, h1532, hc03, hc45, hlam, hphi, ht0b, ht5b, p1533_1]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          rcases p1533_3 (m.d 0 3) (by simp) with h1537 | h1537
                                          · rcases p1533_3 (m.d 1 3) (by simp) with h1538 | h1538
                                            · rcases p1533_3 (m.d 2 3) (by simp) with h1539 | h1539
                                              · linarith only [h1518, h1539, hlam]
                                              · linarith only [h1529, h1539, hlam]
                                            · linarith only [h1526, h1538, hlam]
                                          · linarith only [h1537, hlam, p1533_0]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          rcases p1533_3 (m.d 0 3) (by simp) with h1544 | h1544
                                          · rcases p1533_3 (m.d 1 3) (by simp) with h1545 | h1545
                                            · rcases p1533_3 (m.d 2 3) (by simp) with h1546 | h1546
                                              · linarith only [h1518, h1546, hlam]
                                              · linarith only [h1530, h1546, hlam]
                                            · linarith only [h1527, h1545, hlam]
                                          · linarith only [h1544, hlam, p1533_0]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [h1250, h1516, h1524, h1529, h1532, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1533_1]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [hlam, p1533_0]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [h1523, h1529, h1532, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1533_1]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          rcases p1533_3 (m.d 0 3) (by simp) with h1554 | h1554
                                          · linarith only [h1250, h1554, hlam]
                                          · linarith only [h1520, h1554, hlam]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          rcases p1533_3 (m.d 0 3) (by simp) with h1557 | h1557
                                          · linarith only [h1250, h1557, hlam]
                                          · linarith only [h1521, h1557, hlam]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [h1518, hlam, p1533_0]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [h1523, hlam, p1533_0]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [hlam, p1533_0]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [h1518, h1532, hc02, hc45, hlam, hphi, ht0b, ht5b, p1533_1]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          rcases p1533_3 (m.d 0 3) (by simp) with h1564 | h1564
                                          · rcases p1533_3 (m.d 1 3) (by simp) with h1565 | h1565
                                            · rcases p1533_3 (m.d 2 3) (by simp) with h1566 | h1566
                                              · rcases p1533_3 (m.d 3 4) (by simp) with h1567 | h1567
                                                · linarith only [h1529, h1567, hlam]
                                                · linarith only [h1532, h1567, hlam]
                                              · linarith only [h1566, hlam, p1533_0]
                                            · linarith only [h1527, h1565, hlam]
                                          · linarith only [h1521, h1564, hlam]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [h1520, hlam, p1533_0]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [h1526, hlam, p1533_0]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [h1529, hlam, p1533_0]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [hlam, p1533_0]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [h0, h1516, h1524, h1529, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1533_1]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [h1521, hlam, p1533_0]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [h1527, hlam, p1533_0]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [h1530, hlam, p1533_0]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [h1532, hlam, p1533_0]
                                        · obtain ⟨p1533_0, p1533_1, p1533_2, p1533_3⟩ := h1533c
                                          linarith only [hlam, p1533_0]
                                      · linarith only [h1532, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h1250, h1516, h1523, h1528, h1531, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h1529, h1530, hc34, hlam, hphi, ht45, u5elo3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1586 | h1586
                                  · linarith only [h1250, h1516, h1523, h1526, h1529, h1586, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h1586, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h1528, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h1250, h1527, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · linarith only [h1250, h1517, h1520, h1526, hc03, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h1525, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h1250, h1516, h1519, h1523, h1524, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h1518, h1523, hlam]
                  · linarith only [h1522, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h1250, h1516, h1521, hc14, hlam, hphi, ht45, u5elo3]
              · linarith only [h1250, h1516, h1520, hlam]
            · linarith only [h0, h1516, h1519, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1599 | h1599
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1600 | h1600
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1601 | h1601
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1602 | h1602
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1603 | h1603
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1604 | h1604
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1605 | h1605
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1606 | h1606
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1607 | h1607
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1608 | h1608
                              · linarith only [h0, h1516, h1518, h1603, h1608, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h1608, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h1516, h1518, h1603, h1604, h1607, hc24, hlam, hphi, ht45, u5elo3]
                          · linarith only [h0, h1516, h1518, h1600, h1603, h1604, h1606, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h1516, h1518, h1603, h1604, h1605, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h1516, h1518, h1603, h1604, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1615 | h1615
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1616 | h1616
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1617 | h1617
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1618 | h1618
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1619 | h1619
                              · linarith only [h0, h1516, h1603, h1619, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h1619, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h1250, h1618, hc03, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h0, h1516, h1600, h1603, h1615, h1617, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h1516, h1615, h1616, hc24, hlam, hphi, ht45, u5elo2]
                      · linarith only [h0, h1516, h1599, h1615, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h1602, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h1518, h1601, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h1516, h1518, h1600, hlam]
            · linarith only [h0, h1516, h1599, hlam]
        · linarith only [h1516, h1517, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1631 | h1631
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1632 | h1632
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1633 | h1633
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1634 | h1634
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1635 | h1635
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1636 | h1636
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1637 | h1637
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1638 | h1638
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1639 | h1639
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1640 | h1640
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1641 | h1641
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1642 | h1642
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1643 | h1643
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1644 | h1644
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1645 | h1645
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1646 | h1646
                                      · rcases h3bigk with h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [hlam, p1647_0]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [h1250, hlam, p1647_1]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [h1643, h1646, hc03, hc45, hlam, hphi, ht0b, ht5b, p1647_1]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          rcases p1647_3 (m.d 0 3) (by simp) with h1651 | h1651
                                          · rcases p1647_3 (m.d 1 3) (by simp) with h1652 | h1652
                                            · rcases p1647_3 (m.d 2 3) (by simp) with h1653 | h1653
                                              · linarith only [h1632, h1653, hlam]
                                              · linarith only [h1643, h1653, hlam]
                                            · linarith only [h1640, h1652, hlam]
                                          · linarith only [h1651, hlam, p1647_0]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          rcases p1647_3 (m.d 0 3) (by simp) with h1658 | h1658
                                          · rcases p1647_3 (m.d 1 3) (by simp) with h1659 | h1659
                                            · rcases p1647_3 (m.d 2 3) (by simp) with h1660 | h1660
                                              · linarith only [h1632, h1660, hlam]
                                              · linarith only [h1644, h1660, hlam]
                                            · linarith only [h1641, h1659, hlam]
                                          · linarith only [h1658, hlam, p1647_0]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [h1632, h1643, h1646, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1647_1]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [hlam, p1647_0]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [h1637, h1643, h1646, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1647_1]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          rcases p1647_3 (m.d 0 3) (by simp) with h1668 | h1668
                                          · linarith only [h1250, h1668, hlam]
                                          · linarith only [h1634, h1668, hlam]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          rcases p1647_3 (m.d 0 3) (by simp) with h1671 | h1671
                                          · linarith only [h1250, h1671, hlam]
                                          · linarith only [h1635, h1671, hlam]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [h1632, hlam, p1647_0]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [h1637, hlam, p1647_0]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [hlam, p1647_0]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [h1632, h1646, hc02, hc45, hlam, hphi, ht0b, ht5b, p1647_1]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          rcases p1647_3 (m.d 0 3) (by simp) with h1678 | h1678
                                          · rcases p1647_3 (m.d 1 3) (by simp) with h1679 | h1679
                                            · rcases p1647_3 (m.d 2 3) (by simp) with h1680 | h1680
                                              · rcases p1647_3 (m.d 3 4) (by simp) with h1681 | h1681
                                                · linarith only [h1643, h1681, hlam]
                                                · linarith only [h1646, h1681, hlam]
                                              · linarith only [h1680, hlam, p1647_0]
                                            · linarith only [h1641, h1679, hlam]
                                          · linarith only [h1635, h1678, hlam]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [h1634, hlam, p1647_0]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [h1640, hlam, p1647_0]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [h1643, hlam, p1647_0]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [hlam, p1647_0]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [h0, h1632, h1643, h1646, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1647_1]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [h1635, hlam, p1647_0]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [h1641, hlam, p1647_0]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [h1644, hlam, p1647_0]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [h1646, hlam, p1647_0]
                                        · obtain ⟨p1647_0, p1647_1, p1647_2, p1647_3⟩ := h1647c
                                          linarith only [hlam, p1647_0]
                                      · linarith only [h1646, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h1642, h1645, hc24, hlam, hphi, ht45, u5elo1]
                                  · linarith only [h1644, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1700 | h1700
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1701 | h1701
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1702 | h1702
                                      · rcases h3bigk with h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [hlam, p1703_0]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [h1250, hlam, p1703_1]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          rcases p1703_3 (m.d 0 3) (by simp) with h1706 | h1706
                                          · rcases p1703_3 (m.d 1 3) (by simp) with h1707 | h1707
                                            · rcases p1703_3 (m.d 2 3) (by simp) with h1708 | h1708
                                              · linarith only [h1632, h1708, hlam]
                                              · rcases p1703_3 (m.d 3 4) (by simp) with h1710 | h1710
                                                · linarith only [h1634, h1710, hlam]
                                                · linarith only [h1643, h1710, hlam]
                                            · linarith only [h1637, h1707, hlam]
                                          · linarith only [h1632, h1706, hlam]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [h1632, h1643, h1700, h1702, hc02, hc45, hlam, hphi, ht0b, ht5b, p1703_1]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [h1634, h1643, h1700, hlam, p1703_2]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [h1634, h1643, h1700, h1702, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1703_1]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [hlam, p1703_0]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          rcases p1703_3 (m.d 0 3) (by simp) with h1719 | h1719
                                          · linarith only [h1250, h1719, hlam]
                                          · linarith only [h1632, h1719, hlam]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [h1637, h1643, h1700, h1702, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1703_1]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [h1250, h1634, h1643, h1700, hlam, p1703_2]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [h1632, hlam, p1703_0]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [h1637, hlam, p1703_0]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [hlam, p1703_0]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [h1643, hlam, p1703_0]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [h1634, h1643, h1702, hc03, hc45, hlam, hphi, ht0b, ht5b, p1703_1]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [h1634, hlam, p1703_0]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [h1640, hlam, p1703_0]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [h0, h1632, h1634, h1700, h1702, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1703_1]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [hlam, p1703_0]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          rcases p1703_3 (m.d 0 3) (by simp) with h1733 | h1733
                                          · rcases p1703_3 (m.d 1 3) (by simp) with h1734 | h1734
                                            · rcases p1703_3 (m.d 2 3) (by simp) with h1735 | h1735
                                              · linarith only [h1643, h1735, hlam]
                                              · linarith only [h1700, h1735, hlam]
                                            · linarith only [h1641, h1734, hlam]
                                          · linarith only [h1635, h1733, hlam]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [h1635, hlam, p1703_0]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [h1641, hlam, p1703_0]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [h1700, hlam, p1703_0]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [h1702, hlam, p1703_0]
                                        · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                          linarith only [hlam, p1703_0]
                                      · linarith only [h1702, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h1516, h1631, h1642, h1643, h1700, h1701, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h1700, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h1516, h1642, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                            · linarith only [h1516, h1631, h1639, h1640, h1641, hc25, hlam, hphi, u5elo3]
                          · linarith only [h0, h1250, h1632, h1634, h1640, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h1639, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h1250, h1631, h1633, h1637, h1638, hc02, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h1632, h1637, hlam]
                  · linarith only [h1516, h1631, h1636, hc15, hlam, hphi, u5elo4]
                · linarith only [h1516, h1631, h1634, h1635, hc15, hlam, hphi, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1756 | h1756
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1757 | h1757
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1758 | h1758
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1759 | h1759
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1760 | h1760
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1761 | h1761
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1762 | h1762
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1763 | h1763
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1764 | h1764
                                · linarith only [h1632, h1634, h1764, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1766 | h1766
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1767 | h1767
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1768 | h1768
                                      · rcases h3bigk with h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [hlam, p1769_0]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [h1250, hlam, p1769_1]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [h1634, h1758, h1761, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1769_1]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [h1634, hlam, p1769_0]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [h1634, h1758, h1761, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1769_1]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          rcases p1769_3 (m.d 0 3) (by simp) with h1775 | h1775
                                          · linarith only [h1250, h1775, hlam]
                                          · rcases p1769_3 (m.d 1 3) (by simp) with h1777 | h1777
                                            · rcases p1769_3 (m.d 2 3) (by simp) with h1778 | h1778
                                              · linarith only [h1758, h1778, hlam]
                                              · rcases p1769_3 (m.d 3 4) (by simp) with h1780 | h1780
                                                · linarith only [h1761, h1780, hlam]
                                                · linarith only [h1634, h1780, hlam]
                                            · linarith only [h1250, h1777, hlam]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [hlam, p1769_0]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          rcases p1769_3 (m.d 0 3) (by simp) with h1785 | h1785
                                          · linarith only [h1250, h1785, hlam]
                                          · linarith only [h1632, h1785, hlam]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [h1250, h1631, h1634, h1758, h1760, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1769_1]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [h1632, h1634, h1761, h1766, hlam, p1769_2]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [h1632, hlam, p1769_0]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [h1758, hlam, p1769_0]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [hlam, p1769_0]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [h1764, hlam, p1769_0]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [h1632, h1634, h1761, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p1769_1]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [h1250, h1631, h1760, h1761, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p1769_1]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [h1761, hlam, p1769_0]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [h1758, h1761, h1766, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1769_1]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [hlam, p1769_0]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          rcases p1769_3 (m.d 0 3) (by simp) with h1799 | h1799
                                          · linarith only [h1634, h1799, hlam]
                                          · linarith only [h1756, h1799, hlam]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [h1756, hlam, p1769_0]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [h1762, hlam, p1769_0]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [h1766, hlam, p1769_0]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [h1768, hlam, p1769_0]
                                        · obtain ⟨p1769_0, p1769_1, p1769_2, p1769_3⟩ := h1769c
                                          linarith only [hlam, p1769_0]
                                      · linarith only [h1768, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h1250, h1631, h1634, h1758, h1761, h1763, h1767, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h1766, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h1250, h1634, h1761, h1763, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                            · linarith only [h1250, h1631, h1634, h1760, h1761, h1762, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1812 | h1812
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1813 | h1813
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1814 | h1814
                                · linarith only [h0, h1250, h1631, h1632, h1760, h1761, h1814, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1816 | h1816
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1817 | h1817
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1818 | h1818
                                      · rcases h3bigk with h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [hlam, p1819_0]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [h1250, hlam, p1819_1]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [h1250, h1761, hc23, hc34, hlam, hphi, p1819_1]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [h1634, hlam, p1819_0]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          rcases p1819_3 (m.d 0 3) (by simp) with h1824 | h1824
                                          · rcases p1819_3 (m.d 1 3) (by simp) with h1825 | h1825
                                            · rcases p1819_3 (m.d 2 3) (by simp) with h1826 | h1826
                                              · linarith only [h1632, h1826, hlam]
                                              · linarith only [h1816, h1826, hlam]
                                            · linarith only [h1812, h1825, hlam]
                                          · linarith only [h1824, hlam, p1819_0]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [h1761, hc03, hc34, hlam, hphi, p1819_1]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [hlam, p1819_0]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [h1761, h1816, h1818, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1819_1]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [h1761, hlam, p1819_0]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          rcases p1819_3 (m.d 0 3) (by simp) with h1835 | h1835
                                          · linarith only [h1250, h1835, hlam]
                                          · linarith only [h1756, h1835, hlam]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [h1632, hlam, p1819_0]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [h1758, hlam, p1819_0]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [hlam, p1819_0]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [h1814, hlam, p1819_0]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          rcases p1819_3 (m.d 0 3) (by simp) with h1842 | h1842
                                          · rcases p1819_3 (m.d 1 3) (by simp) with h1843 | h1843
                                            · rcases p1819_3 (m.d 2 3) (by simp) with h1844 | h1844
                                              · rcases p1819_3 (m.d 3 4) (by simp) with h1845 | h1845
                                                · rcases p1819_3 (m.d 3 5) (by simp) with h1846 | h1846
                                                  · linarith only [h1846, hlam, p1819_0]
                                                  · rcases h4bigk with h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [hlam, p1848_0]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [h1516, hlam, p1848_1]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [h1814, h1818, hc04, hc45, hlam, hphi, ht0b, ht5b, p1819_1, p1848_1]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [h1634, hlam, p1848_0]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      rcases p1848_3 (m.d 0 4) (by simp) with h1853 | h1853
                                                      · rcases p1848_3 (m.d 1 4) (by simp) with h1854 | h1854
                                                        · rcases p1848_3 (m.d 2 4) (by simp) with h1855 | h1855
                                                          · linarith only [h1633, h1855, hlam]
                                                          · linarith only [h1817, h1855, hlam]
                                                        · linarith only [h1813, h1854, hlam]
                                                      · linarith only [h1853, hlam, p1848_0]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [h1516, h1631, h1760, h1816, h1818, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1848_1]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [hlam, p1848_0]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [h1759, h1814, h1818, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1819_1, p1848_1]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [h1761, hlam, p1848_0]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      rcases p1848_3 (m.d 0 4) (by simp) with h1864 | h1864
                                                      · linarith only [h1516, h1864, hlam]
                                                      · linarith only [h1757, h1864, hlam]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [h1633, hlam, p1848_1]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [h1759, hlam, p1848_1]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [hlam, p1848_0]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [h1814, hlam, p1848_1]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [h0, h1633, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1848_1]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [h1516, h1631, h1760, h1816, h1818, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1848_1]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [h1516, h1631, h1760, h1816, h1818, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1848_1]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [h1814, h1818, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1819_1, p1848_1]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [hlam, p1848_0]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      rcases p1848_3 (m.d 0 4) (by simp) with h1876 | h1876
                                                      · linarith only [h1634, h1876, hlam]
                                                      · linarith only [h1757, h1876, hlam]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [h1757, hlam, p1848_0]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [h1813, hlam, p1848_0]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [h1817, hlam, p1848_0]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [h1818, hlam, p1848_0]
                                                    · obtain ⟨p1848_0, p1848_1, p1848_2, p1848_3⟩ := h1848c
                                                      linarith only [hlam, p1848_0]
                                                · linarith only [h1818, h1845, hlam]
                                              · linarith only [h1844, hlam, p1819_0]
                                            · linarith only [h1812, h1843, hlam]
                                          · linarith only [h1756, h1842, hlam]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          rcases p1819_3 (m.d 0 3) (by simp) with h1888 | h1888
                                          · linarith only [h1888, hlam, p1819_0]
                                          · rcases p1819_3 (m.d 1 3) (by simp) with h1890 | h1890
                                            · linarith only [h1761, h1890, hlam]
                                            · linarith only [h1250, h1890, hlam]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [h1250, h1631, h1760, h1816, h1818, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1819_1]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          rcases p1819_3 (m.d 0 3) (by simp) with h1894 | h1894
                                          · linarith only [h1634, h1894, hlam]
                                          · linarith only [h1632, h1894, hlam]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [hlam, p1819_0]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [h1250, h1631, h1760, h1761, h1816, hlam, p1819_2]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [h1756, hlam, p1819_0]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [h1812, hlam, p1819_0]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [h1816, hlam, p1819_0]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [h1818, hlam, p1819_0]
                                        · obtain ⟨p1819_0, p1819_1, p1819_2, p1819_3⟩ := h1819c
                                          linarith only [hlam, p1819_0]
                                      · linarith only [h1250, h1631, h1760, h1761, h1816, h1818, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                    · linarith only [h1250, h1631, h1761, h1813, h1814, h1817, hc23, hc34, hlam, hphi]
                                  · linarith only [h1816, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h1250, h1631, h1760, h1761, h1813, hc25, hlam, hphi, u5elo4]
                            · linarith only [h1250, h1631, h1760, h1812, hc25, hlam, hphi, u5elo3]
                        · linarith only [h0, h1760, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h1250, h1631, h1633, h1758, h1759, hc02, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h1632, h1758, hlam]
                  · linarith only [h1250, h1631, h1634, h1757, hc15, hlam, hphi, u5elo4]
                · linarith only [h1250, h1631, h1756, hc15, hlam, hphi, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1914 | h1914
              · linarith only [h1632, h1633, h1914, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1916 | h1916
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1917 | h1917
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1918 | h1918
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1919 | h1919
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1920 | h1920
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1921 | h1921
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1922 | h1922
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1923 | h1923
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1924 | h1924
                                · linarith only [h1250, h1631, h1632, h1914, h1920, h1924, hc02, hc25, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1926 | h1926
                                  · linarith only [h1632, h1633, h1921, h1924, h1926, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h1926, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h1923, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h1922, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1931 | h1931
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1932 | h1932
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1933 | h1933
                                · linarith only [h1250, h1631, h1632, h1920, h1921, h1933, hc02, hc25, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1935 | h1935
                                  · linarith only [h1632, h1633, h1919, h1935, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h1935, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h1932, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h1250, h1631, h1920, h1931, hc25, hlam, hphi, u5elo3]
                        · linarith only [h1633, h1919, h1920, hc02, hc25, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1941 | h1941
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1942 | h1942
                          · linarith only [h1250, h1914, h1918, h1919, h1942, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1944 | h1944
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1945 | h1945
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1946 | h1946
                                · linarith only [h1250, h1631, h1941, h1942, h1946, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1948 | h1948
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1949 | h1949
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1950 | h1950
                                      · rcases h3bigk with h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c | h1951c
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [hlam, p1951_0]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [h1250, hlam, p1951_1]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [h0, h1632, h1919, h1946, hc23, hc34, hlam, hphi, p1951_1]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [h1914, hlam, p1951_0]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          rcases p1951_3 (m.d 0 3) (by simp) with h1956 | h1956
                                          · rcases p1951_3 (m.d 1 3) (by simp) with h1957 | h1957
                                            · rcases p1951_3 (m.d 2 3) (by simp) with h1958 | h1958
                                              · linarith only [h1632, h1958, hlam]
                                              · linarith only [h1948, h1958, hlam]
                                            · linarith only [h1944, h1957, hlam]
                                          · linarith only [h1956, hlam, p1951_0]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [h1918, h1919, h1946, hc03, hc34, hlam, hphi, p1951_1]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [hlam, p1951_0]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [h1918, h1919, h1946, h1948, h1950, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1951_1]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [h1942, hlam, p1951_0]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          rcases p1951_3 (m.d 0 3) (by simp) with h1967 | h1967
                                          · linarith only [h1250, h1967, hlam]
                                          · linarith only [h1916, h1967, hlam]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [h1632, hlam, p1951_0]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [h1918, hlam, p1951_0]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [hlam, p1951_0]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [h1946, hlam, p1951_0]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [h0, h1632, h1919, h1946, h1950, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1951_1]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          rcases p1951_3 (m.d 0 3) (by simp) with h1975 | h1975
                                          · linarith only [h1975, hlam, p1951_0]
                                          · rcases p1951_3 (m.d 1 3) (by simp) with h1977 | h1977
                                            · linarith only [h1942, h1977, hlam]
                                            · linarith only [h1250, h1977, hlam]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [h1250, hc01, hc34, hlam, hphi, ht12, ht23, p1951_1]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          rcases p1951_3 (m.d 0 3) (by simp) with h1981 | h1981
                                          · linarith only [h1914, h1981, hlam]
                                          · linarith only [h1632, h1981, hlam]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [hlam, p1951_0]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [h0, h1631, h1919, h1941, h1946, h1948, hlam, p1951_2]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [h1916, hlam, p1951_0]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [h1944, hlam, p1951_0]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [h1948, hlam, p1951_0]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [h1950, hlam, p1951_0]
                                        · obtain ⟨p1951_0, p1951_1, p1951_2, p1951_3⟩ := h1951c
                                          linarith only [hlam, p1951_0]
                                      · linarith only [h1250, h1918, h1919, h1946, h1950, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                    · linarith only [h1250, h1631, h1918, h1919, h1945, h1949, hlam]
                                  · linarith only [h1948, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h1516, h1945, hc04, hlam, hphi, ht45, u5elo4]
                            · linarith only [h1250, h1631, h1941, h1944, hc25, hlam, hphi, u5elo3]
                        · linarith only [h1250, h1918, h1941, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h1632, h1918, hlam]
                  · linarith only [h1917, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h1916, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2000 | h2000
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2001 | h2001
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2002 | h2002
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2003 | h2003
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2004 | h2004
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2005 | h2005
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2006 | h2006
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2007 | h2007
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2008 | h2008
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2009 | h2009
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h2010 | h2010
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h2011 | h2011
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2012 | h2012
                                    · linarith only [h1632, h2000, h2004, h2012, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h2012, hc24, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h1516, h1632, h2000, h2011, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                                · linarith only [h1516, h1631, h1632, h2000, h2001, h2010, hc03, hc15, hlam, hphi, ht0b, ht5b]
                              · linarith only [h1516, h1631, h2006, h2009, hc25, hlam, hphi, u5elo4]
                            · linarith only [h2008, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h1632, h2000, h2001, h2004, h2007, hlam]
                        · linarith only [h1516, h1632, h2000, h2004, h2006, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h1516, h1631, h1632, h2000, h2004, h2005, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2022 | h2022
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2023 | h2023
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2024 | h2024
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2025 | h2025
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2026 | h2026
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h2027 | h2027
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h2028 | h2028
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2029 | h2029
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2030 | h2030
                                      · rcases h3bigk with h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [hlam, p2031_0]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [h1250, hlam, p2031_1]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [h1632, hlam, p2031_1]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          rcases p2031_3 (m.d 0 3) (by simp) with h2035 | h2035
                                          · rcases p2031_3 (m.d 1 3) (by simp) with h2036 | h2036
                                            · rcases p2031_3 (m.d 2 3) (by simp) with h2037 | h2037
                                              · rcases p2031_3 (m.d 3 4) (by simp) with h2038 | h2038
                                                · linarith only [h2038, hlam, p2031_0]
                                                · rcases p2031_3 (m.d 3 5) (by simp) with h2040 | h2040
                                                  · linarith only [h2002, h2040, hlam]
                                                  · rcases h4bigk with h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [hlam, p2042_0]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h1516, hlam, p2042_1]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h2027, h2030, hc04, hc45, hlam, hphi, ht0b, ht5b, p2042_1]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h2000, h2030, hc02, hc45, hlam, hphi, ht0b, ht5b, p2042_1]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h1516, h2004, h2022, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2042_1]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h2004, h2022, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2042_1]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [hlam, p2042_0]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h2004, h2022, h2027, h2030, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2042_1]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h2004, h2022, h2030, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2042_1]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h2004, h2022, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2042_1]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h2000, hlam, p2042_1]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h2022, hlam, p2042_1]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [hlam, p2042_0]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h2030, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2042_1]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h1516, h2000, h2004, h2022, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2042_1]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h2001, hlam, p2042_1]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h2024, hlam, p2042_1]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h2027, hlam, p2042_0]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [hlam, p2042_0]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h1250, h2004, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2031_1, p2042_1]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h2003, hlam, p2042_0]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h2026, hlam, p2042_0]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h2029, hlam, p2042_0]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [h2030, hlam, p2042_0]
                                                    · obtain ⟨p2042_0, p2042_1, p2042_2, p2042_3⟩ := h2042c
                                                      linarith only [hlam, p2042_0]
                                              · linarith only [h2027, h2037, hlam]
                                            · linarith only [h2024, h2036, hlam]
                                          · linarith only [h2035, hlam, p2031_0]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          rcases p2031_3 (m.d 0 3) (by simp) with h2071 | h2071
                                          · rcases p2031_3 (m.d 1 3) (by simp) with h2072 | h2072
                                            · rcases p2031_3 (m.d 2 3) (by simp) with h2073 | h2073
                                              · rcases p2031_3 (m.d 3 4) (by simp) with h2074 | h2074
                                                · linarith only [h2001, h2074, hlam]
                                                · linarith only [h2030, h2074, hlam]
                                              · linarith only [h2028, h2073, hlam]
                                            · linarith only [h2025, h2072, hlam]
                                          · linarith only [h2071, hlam, p2031_0]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [h1632, h2000, h2004, h2029, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2031_1]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [hlam, p2031_0]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [h2004, hlam, p2031_1]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          rcases p2031_3 (m.d 0 3) (by simp) with h2083 | h2083
                                          · linarith only [h1250, h2083, hlam]
                                          · linarith only [h2001, h2083, hlam]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          rcases p2031_3 (m.d 0 3) (by simp) with h2086 | h2086
                                          · linarith only [h1250, h2086, hlam]
                                          · linarith only [h2002, h2086, hlam]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [h1632, h2000, h2027, h2030, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2031_1]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [h1250, h1631, h2023, h2028, h2030, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2031_1]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [hlam, p2031_0]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          rcases p2031_3 (m.d 0 3) (by simp) with h2092 | h2092
                                          · linarith only [h1632, h2092, hlam]
                                          · linarith only [h2001, h2092, hlam]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [h0, h1631, h2004, h2023, h2028, hlam, p2031_2]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [h2001, hlam, p2031_0]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [h2024, hlam, p2031_0]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [h2027, hlam, p2031_0]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [hlam, p2031_0]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [h0, h2000, h2004, h2027, h2030, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2031_1]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [h2002, hlam, p2031_0]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [h2025, hlam, p2031_0]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [h2028, hlam, p2031_0]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [h2030, hlam, p2031_0]
                                        · obtain ⟨p2031_0, p2031_1, p2031_2, p2031_3⟩ := h2031c
                                          linarith only [hlam, p2031_0]
                                      · linarith only [h2030, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h1631, h2026, h2029, hc24, hlam, hphi, ht45, u5elo0]
                                  · linarith only [h1516, h2004, h2022, h2028, hc01, hc35, hlam, hphi, ht12, ht23]
                                · linarith only [h1516, h1631, h2004, h2022, h2026, h2027, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1516, h2026, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                            · linarith only [h1516, h1631, h2004, h2022, h2023, h2025, hc25, hlam, hphi, u5elo3]
                          · linarith only [h1516, h1631, h2001, h2004, h2022, h2023, h2024, hc03, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h1516, h2022, h2023, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h1631, h2000, h2022, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1516, h1631, h2003, hc15, hlam, hphi, u5elo4]
                · linarith only [h2002, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h1632, h2000, h2001, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2118 | h2118
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2119 | h2119
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2120 | h2120
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2121 | h2121
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2122 | h2122
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2123 | h2123
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2124 | h2124
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2125 | h2125
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2126 | h2126
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h2127 | h2127
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h2128 | h2128
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2129 | h2129
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2130 | h2130
                                      · rcases h3bigk with h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [hlam, p2131_0]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [h1250, hlam, p2131_1]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [h1632, hlam, p2131_1]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [h1632, h2121, h2130, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2131_1]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          rcases p2131_3 (m.d 0 3) (by simp) with h2136 | h2136
                                          · rcases p2131_3 (m.d 1 3) (by simp) with h2137 | h2137
                                            · rcases p2131_3 (m.d 2 3) (by simp) with h2138 | h2138
                                              · rcases p2131_3 (m.d 3 4) (by simp) with h2139 | h2139
                                                · linarith only [h2118, h2139, hlam]
                                                · linarith only [h2130, h2139, hlam]
                                              · linarith only [h2128, h2138, hlam]
                                            · linarith only [h2125, h2137, hlam]
                                          · linarith only [h2136, hlam, p2131_0]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [h2118, h2130, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2131_1]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [hlam, p2131_0]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [h0, h1631, h1632, h2121, h2123, h2128, h2130, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2131_1]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          rcases p2131_3 (m.d 0 3) (by simp) with h2148 | h2148
                                          · linarith only [h1250, h2148, hlam]
                                          · linarith only [h2118, h2148, hlam]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          rcases p2131_3 (m.d 0 3) (by simp) with h2151 | h2151
                                          · linarith only [h1250, h2151, hlam]
                                          · linarith only [h2119, h2151, hlam]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [h2118, h2130, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2131_1]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [h2121, hlam, p2131_0]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [hlam, p2131_0]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [h2121, h2130, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2131_1]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          rcases p2131_3 (m.d 0 3) (by simp) with h2158 | h2158
                                          · linarith only [h1632, h2158, hlam]
                                          · linarith only [h2119, h2158, hlam]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [h2118, hlam, p2131_0]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [h2124, hlam, p2131_0]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [h2127, hlam, p2131_0]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [hlam, p2131_0]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [h1632, h2118, h2121, h2130, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2131_1]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [h2119, hlam, p2131_0]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [h2125, hlam, p2131_0]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [h2128, hlam, p2131_0]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [h2130, hlam, p2131_0]
                                        · obtain ⟨p2131_0, p2131_1, p2131_2, p2131_3⟩ := h2131c
                                          linarith only [hlam, p2131_0]
                                      · linarith only [h2130, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h0, h1631, h2000, h2126, h2129, hlam]
                                  · linarith only [h1632, h2128, hc03, hlam, hphi, ht34, ht45, u5elo3]
                                · linarith only [h0, h1631, h1632, h2118, h2127, hc03, hc15, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h1631, h2000, h2122, h2123, h2126, hc25, hlam, hphi, u5elo4]
                            · linarith only [h2125, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h1632, h2118, h2121, h2124, hlam]
                        · linarith only [h2123, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h1631, h1632, h2121, h2122, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2180 | h2180
                      · linarith only [h0, h1631, h2000, h2121, h2180, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2182 | h2182
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2183 | h2183
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2184 | h2184
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2185 | h2185
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h2186 | h2186
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h2187 | h2187
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2188 | h2188
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2189 | h2189
                                      · rcases h3bigk with h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [hlam, p2190_0]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [h1250, hlam, p2190_1]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [h1632, hlam, p2190_1]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          rcases p2190_3 (m.d 0 3) (by simp) with h2194 | h2194
                                          · rcases p2190_3 (m.d 1 3) (by simp) with h2195 | h2195
                                            · rcases p2190_3 (m.d 2 3) (by simp) with h2196 | h2196
                                              · rcases p2190_3 (m.d 3 4) (by simp) with h2197 | h2197
                                                · linarith only [h2197, hlam, p2190_0]
                                                · rcases p2190_3 (m.d 3 5) (by simp) with h2199 | h2199
                                                  · linarith only [h2119, h2199, hlam]
                                                  · rcases h4bigk with h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [hlam, p2201_0]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [h1516, hlam, p2201_1]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [h2000, hlam, p2201_0]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [h2118, hlam, p2190_2, p2201_1]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      rcases p2201_3 (m.d 0 4) (by simp) with h2206 | h2206
                                                      · rcases p2201_3 (m.d 1 4) (by simp) with h2207 | h2207
                                                        · rcases p2201_3 (m.d 2 4) (by simp) with h2208 | h2208
                                                          · rcases p2201_3 (m.d 3 4) (by simp) with h2209 | h2209
                                                            · linarith only [h2118, h2209, hlam]
                                                            · linarith only [h2189, h2209, hlam]
                                                          · linarith only [h2188, h2208, hlam]
                                                        · linarith only [h2185, h2207, hlam]
                                                      · linarith only [h2206, hlam, p2201_0]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [h1516, h1631, h2121, h2182, h2183, h2187, h2189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2201_1]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [hlam, p2201_0]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [h2180, hlam, p2201_0]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [h2121, h2183, h2189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2201_1]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      rcases p2201_3 (m.d 0 4) (by simp) with h2219 | h2219
                                                      · linarith only [h1516, h2219, hlam]
                                                      · linarith only [h2120, h2219, hlam]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [h0, h1631, h2000, h2182, h2186, h2187, h2189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2201_1]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [h1516, h1631, h2182, h2186, h2187, h2189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2201_1]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [hlam, p2201_0]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [h2186, h2189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2201_1]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      rcases p2201_3 (m.d 0 4) (by simp) with h2226 | h2226
                                                      · linarith only [h2000, h2226, hlam]
                                                      · linarith only [h2120, h2226, hlam]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [h2118, hlam, p2201_1]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [h2183, hlam, p2201_1]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [h2186, hlam, p2201_0]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [hlam, p2201_0]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [h1250, h2121, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2190_1, p2201_1]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [h2120, hlam, p2201_0]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [h2185, hlam, p2201_0]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [h2188, hlam, p2201_0]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [h2189, hlam, p2201_0]
                                                    · obtain ⟨p2201_0, p2201_1, p2201_2, p2201_3⟩ := h2201c
                                                      linarith only [hlam, p2201_0]
                                              · linarith only [h2186, h2196, hlam]
                                            · linarith only [h2183, h2195, hlam]
                                          · linarith only [h2194, hlam, p2190_0]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          rcases p2190_3 (m.d 0 3) (by simp) with h2242 | h2242
                                          · rcases p2190_3 (m.d 1 3) (by simp) with h2243 | h2243
                                            · rcases p2190_3 (m.d 2 3) (by simp) with h2244 | h2244
                                              · rcases p2190_3 (m.d 3 4) (by simp) with h2245 | h2245
                                                · linarith only [h2118, h2245, hlam]
                                                · linarith only [h2189, h2245, hlam]
                                              · linarith only [h2187, h2244, hlam]
                                            · linarith only [h2184, h2243, hlam]
                                          · linarith only [h2242, hlam, p2190_0]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [h2118, h2121, h2189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2190_1]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [hlam, p2190_0]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [h2121, hlam, p2190_1]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          rcases p2190_3 (m.d 0 3) (by simp) with h2254 | h2254
                                          · linarith only [h1250, h2254, hlam]
                                          · linarith only [h2118, h2254, hlam]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          rcases p2190_3 (m.d 0 3) (by simp) with h2257 | h2257
                                          · linarith only [h1250, h2257, hlam]
                                          · linarith only [h2119, h2257, hlam]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [h2118, h2189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2190_1]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [h1250, h1631, h2182, h2187, h2189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2190_1]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [hlam, p2190_0]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          rcases p2190_3 (m.d 0 3) (by simp) with h2263 | h2263
                                          · linarith only [h1632, h2263, hlam]
                                          · linarith only [h2118, h2263, hlam]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [h0, h1631, h2121, h2182, h2187, hlam, p2190_2]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [h2118, hlam, p2190_0]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [h2183, hlam, p2190_0]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [h2186, hlam, p2190_0]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [hlam, p2190_0]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          rcases p2190_3 (m.d 0 3) (by simp) with h2271 | h2271
                                          · rcases p2190_3 (m.d 1 3) (by simp) with h2272 | h2272
                                            · rcases p2190_3 (m.d 2 3) (by simp) with h2273 | h2273
                                              · rcases p2190_3 (m.d 3 4) (by simp) with h2274 | h2274
                                                · rcases p2190_3 (m.d 3 5) (by simp) with h2275 | h2275
                                                  · linarith only [h2189, h2275, hlam]
                                                  · rcases h4bigk with h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [hlam, p2277_0]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [h1516, hlam, p2277_1]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [h2000, hlam, p2277_0]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [h2189, hc04, hc45, hlam, hphi, ht0b, ht5b, p2190_1, p2277_1]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      rcases p2277_3 (m.d 0 4) (by simp) with h2282 | h2282
                                                      · rcases p2277_3 (m.d 1 4) (by simp) with h2283 | h2283
                                                        · rcases p2277_3 (m.d 2 4) (by simp) with h2284 | h2284
                                                          · rcases p2277_3 (m.d 3 4) (by simp) with h2285 | h2285
                                                            · linarith only [h2118, h2285, hlam]
                                                            · linarith only [h2189, h2285, hlam]
                                                          · linarith only [h2188, h2284, hlam]
                                                        · linarith only [h2185, h2283, hlam]
                                                      · linarith only [h2282, hlam, p2277_0]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [h1516, h1631, h2182, h2183, h2187, h2189, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2277_1]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [hlam, p2277_0]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [h2180, hlam, p2277_0]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [h2180, h2186, h2189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2190_1, p2277_1]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      rcases p2277_3 (m.d 0 4) (by simp) with h2295 | h2295
                                                      · linarith only [h1516, h2295, hlam]
                                                      · linarith only [h2120, h2295, hlam]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [h2118, h2186, h2189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2190_1, p2277_1]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [h1516, h1631, h2182, h2186, h2187, h2189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2277_1]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [hlam, p2277_0]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [h2186, h2189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2190_1, p2277_1]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      rcases p2277_3 (m.d 0 4) (by simp) with h2302 | h2302
                                                      · linarith only [h2000, h2302, hlam]
                                                      · linarith only [h2120, h2302, hlam]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [h2118, hlam, p2277_1]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [h2183, hlam, p2277_1]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [h2186, hlam, p2277_0]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [hlam, p2277_0]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [h2118, hc03, hc45, hlam, hphi, ht0b, ht5b, p2277_1]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [h2120, hlam, p2277_0]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [h2185, hlam, p2277_0]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [h2188, hlam, p2277_0]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [h2189, hlam, p2277_0]
                                                    · obtain ⟨p2277_0, p2277_1, p2277_2, p2277_3⟩ := h2277c
                                                      linarith only [hlam, p2277_0]
                                                · linarith only [h2189, h2274, hlam]
                                              · linarith only [h2187, h2273, hlam]
                                            · linarith only [h2184, h2272, hlam]
                                          · linarith only [h2119, h2271, hlam]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [h2119, hlam, p2190_0]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [h2184, hlam, p2190_0]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [h2187, hlam, p2190_0]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [h2189, hlam, p2190_0]
                                        · obtain ⟨p2190_0, p2190_1, p2190_2, p2190_3⟩ := h2190c
                                          linarith only [hlam, p2190_0]
                                      · linarith only [h2189, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h0, h2180, h2188, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                  · linarith only [h0, h1631, h2180, h2182, h2186, h2187, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h1250, h1631, h2118, h2121, h2182, h2186, hc03, hc25, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h1631, h2180, h2182, h2185, hc25, hlam, hphi, u5elo4]
                            · linarith only [h0, h1631, h2180, h2182, h2183, h2184, hc25, hlam, hphi, u5elo3]
                          · linarith only [h1250, h2118, h2183, hlam]
                        · linarith only [h0, h2182, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h1631, h2000, h2120, hc15, hlam, hphi, u5elo4]
                · linarith only [h0, h1631, h2000, h2118, h2119, hc15, hlam, hphi, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2334 | h2334
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2335 | h2335
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2336 | h2336
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2337 | h2337
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2338 | h2338
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2339 | h2339
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2340 | h2340
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2341 | h2341
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h2342 | h2342
                                · linarith only [h1250, h1631, h2118, h2336, h2338, h2342, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h0, h1631, h1632, h2338, h2339, h2342, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h2341, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h2340, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2347 | h2347
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2348 | h2348
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h2349 | h2349
                                · linarith only [h2336, h2339, h2349, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h2351 | h2351
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2352 | h2352
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2353 | h2353
                                      · rcases h3bigk with h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [hlam, p2354_0]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [h1250, hlam, p2354_1]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [h1632, hlam, p2354_1]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [h2118, hlam, p2354_0]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          rcases p2354_3 (m.d 0 3) (by simp) with h2359 | h2359
                                          · rcases p2354_3 (m.d 1 3) (by simp) with h2360 | h2360
                                            · rcases p2354_3 (m.d 2 3) (by simp) with h2361 | h2361
                                              · rcases p2354_3 (m.d 3 4) (by simp) with h2362 | h2362
                                                · rcases p2354_3 (m.d 3 5) (by simp) with h2363 | h2363
                                                  · linarith only [h2363, hlam, p2354_0]
                                                  · rcases h4bigk with h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [hlam, p2365_0]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h1516, hlam, p2365_1]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h2000, hlam, p2365_0]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h2118, hlam, p2365_0]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h2000, h2337, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2365_1]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h1516, h1631, h2338, h2351, h2353, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p2365_1]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [hlam, p2365_0]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h0, h1631, h2000, h2337, h2338, h2351, h2353, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2365_1]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h2339, hlam, p2365_0]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      rcases p2365_3 (m.d 0 4) (by simp) with h2375 | h2375
                                                      · linarith only [h1516, h2375, hlam]
                                                      · linarith only [h2335, h2375, hlam]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h2118, h2353, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2354_1, p2365_1]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h2337, hlam, p2365_1]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [hlam, p2365_0]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h2349, hlam, p2365_1]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h2337, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2365_1]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h2118, h2353, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2354_1, p2365_1]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h1516, h1631, h2338, h2351, h2353, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2365_1]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h0, h1631, h2000, h2338, h2351, h2353, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2365_1]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [hlam, p2365_0]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      rcases p2365_3 (m.d 0 4) (by simp) with h2387 | h2387
                                                      · linarith only [h2118, h2387, hlam]
                                                      · linarith only [h2335, h2387, hlam]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h2335, hlam, p2365_0]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h2348, hlam, p2365_0]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h2352, hlam, p2365_0]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [h2353, hlam, p2365_0]
                                                    · obtain ⟨p2365_0, p2365_1, p2365_2, p2365_3⟩ := h2365c
                                                      linarith only [hlam, p2365_0]
                                                · linarith only [h2353, h2362, hlam]
                                              · linarith only [h2351, h2361, hlam]
                                            · linarith only [h2347, h2360, hlam]
                                          · linarith only [h2359, hlam, p2354_0]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [h2339, hc03, hc34, hlam, hphi, p2354_1]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [hlam, p2354_0]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [h0, h1631, h1632, h2338, h2339, h2351, h2353, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2354_1]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [h2339, hlam, p2354_0]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          rcases p2354_3 (m.d 0 3) (by simp) with h2403 | h2403
                                          · linarith only [h1250, h2403, hlam]
                                          · linarith only [h2334, h2403, hlam]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [h0, h1631, h1632, h2336, h2338, h2351, h2353, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2354_1]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [h2336, hlam, p2354_0]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [hlam, p2354_0]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [h2349, hlam, p2354_0]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          rcases p2354_3 (m.d 0 3) (by simp) with h2410 | h2410
                                          · linarith only [h1632, h2410, hlam]
                                          · linarith only [h2334, h2410, hlam]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          rcases p2354_3 (m.d 0 3) (by simp) with h2413 | h2413
                                          · linarith only [h2413, hlam, p2354_0]
                                          · rcases p2354_3 (m.d 1 3) (by simp) with h2415 | h2415
                                            · linarith only [h2339, h2415, hlam]
                                            · linarith only [h1250, h2415, hlam]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [h1250, h1631, h2338, h2351, h2353, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2354_1]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [h0, h1631, h1632, h2338, h2351, h2353, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2354_1]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [hlam, p2354_0]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [h0, h1631, h1632, h2336, h2338, h2339, h2351, hlam, p2354_2]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [h2334, hlam, p2354_0]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [h2347, hlam, p2354_0]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [h2351, hlam, p2354_0]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [h2353, hlam, p2354_0]
                                        · obtain ⟨p2354_0, p2354_1, p2354_2, p2354_3⟩ := h2354c
                                          linarith only [hlam, p2354_0]
                                      · linarith only [h0, h1631, h1632, h2336, h2338, h2339, h2351, h2353, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                    · linarith only [h0, h1631, h1632, h2348, h2349, h2352, hlam]
                                  · linarith only [h0, h1631, h1632, h2338, h2351, hc25, hlam, hphi, u5elo3]
                              · linarith only [h2348, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h1631, h1632, h2336, h2338, h2347, hc25, hlam, hphi, u5elo3]
                        · linarith only [h2338, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h1632, h2336, h2337, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2434 | h2434
                      · linarith only [h0, h1631, h2000, h2336, h2434, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2436 | h2436
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2437 | h2437
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2438 | h2438
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2439 | h2439
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h2440 | h2440
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h2441 | h2441
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2442 | h2442
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2443 | h2443
                                      · rcases h3bigk with h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [hlam, p2444_0]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [h1250, hlam, p2444_1]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [h1632, hlam, p2444_1]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [h2118, hlam, p2444_0]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [h2118, h2437, h2443, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2444_1]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          rcases p2444_3 (m.d 0 3) (by simp) with h2450 | h2450
                                          · linarith only [h1250, h2450, hlam]
                                          · rcases p2444_3 (m.d 1 3) (by simp) with h2452 | h2452
                                            · rcases p2444_3 (m.d 2 3) (by simp) with h2453 | h2453
                                              · rcases p2444_3 (m.d 3 4) (by simp) with h2454 | h2454
                                                · linarith only [h2437, h2454, hlam]
                                                · linarith only [h2118, h2454, hlam]
                                              · linarith only [h1632, h2453, hlam]
                                            · linarith only [h1250, h2452, hlam]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [hlam, p2444_0]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [h2336, hlam, p2444_1]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [h1250, h1631, h2118, h2336, h2436, h2441, h2443, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2444_1]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [h0, h1631, h1632, h2118, h2436, h2437, h2441, hlam, p2444_2]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          rcases p2444_3 (m.d 0 3) (by simp) with h2463 | h2463
                                          · linarith only [h1632, h2463, hlam]
                                          · rcases p2444_3 (m.d 1 3) (by simp) with h2465 | h2465
                                            · linarith only [h2336, h2465, hlam]
                                            · linarith only [h1250, h2465, hlam]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [h0, h1631, h1632, h2118, h2436, h2437, h2441, h2443, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2444_1]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [hlam, p2444_0]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [h0, h1631, h1632, h2118, h2436, h2441, h2443, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2444_1]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [h0, h1631, h2434, h2436, h2440, h2441, hlam, p2444_2]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [h0, h1631, h1632, h2436, h2437, h2441, h2443, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2444_1]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [h2437, hlam, p2444_0]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [h2440, hlam, p2444_0]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [hlam, p2444_0]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          rcases p2444_3 (m.d 0 3) (by simp) with h2476 | h2476
                                          · linarith only [h2118, h2476, hlam]
                                          · linarith only [h2334, h2476, hlam]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [h2334, hlam, p2444_0]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [h2438, hlam, p2444_0]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [h2441, hlam, p2444_0]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [h2443, hlam, p2444_0]
                                        · obtain ⟨p2444_0, p2444_1, p2444_2, p2444_3⟩ := h2444c
                                          linarith only [hlam, p2444_0]
                                      · linarith only [h2443, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h2434, h2442, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                                  · linarith only [h0, h1631, h1632, h2118, h2336, h2436, h2437, h2441, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h2336, h2437, h2440, hlam]
                              · linarith only [h0, h1631, h1632, h2118, h2436, h2437, h2439, hc25, hlam, hphi, u5elo4]
                            · linarith only [h0, h1631, h1632, h2118, h2436, h2437, h2438, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2490 | h2490
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2491 | h2491
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h2492 | h2492
                                · linarith only [h1250, h1631, h2436, h2437, h2492, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h0, h1631, h2336, h2436, h2492, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h2491, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h1631, h2336, h2436, h2490, hc25, hlam, hphi, u5elo3]
                        · linarith only [h0, h2436, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h1632, h2118, h2335, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h0, h1631, h1632, h2334, hc15, hlam, hphi, u5elo3]
        · linarith only [h1631, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 3706000 in
theorem n7l_sAB3_M_IR_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5emax := hb5.2.2
  have h3ehi := hb3.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · rcases h4bigk with h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, h11, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, h11, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, h11, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            rcases p12_3 (m.d 0 4) (by simp) with h17 | h17
                            · rcases p12_3 (m.d 1 4) (by simp) with h18 | h18
                              · linarith only [h0, h18, hlam]
                              · linarith only [h18, h7, hlam]
                            · linarith only [h17, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h11, h8, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p12_1, u4ehi4]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, h11, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h1, hlam, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h5, hlam, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h11, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u4ehi4]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h5, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p12_1, u4ehi4]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h2, hlam, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h6, hlam, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h8, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h2, hc03, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h4, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h7, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h10, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h11, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [hlam, p12_0]
                        · linarith only [h0, h11, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h10, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h8, h9, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
                    · linarith only [h45, h8, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h48 | h48
                        · rcases h4bigk with h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [hlam, p49_0]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h0, h47, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p49_1, u4ehi4]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h0, h47, hc01, hlam, hphi, ht0b, ht45, ht5b, p49_1, u4ehi4]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p49_1, u3ehi2]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            rcases p49_3 (m.d 0 4) (by simp) with h54 | h54
                            · rcases p49_3 (m.d 1 4) (by simp) with h55 | h55
                              · linarith only [h0, h55, hlam]
                              · linarith only [h55, h7, hlam]
                            · linarith only [h54, hlam, p49_0]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h0, hlam, p49_0]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [hlam, p49_0]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h47, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p49_1, u4ehi4]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h0, h45, h48, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p49_1, u3ehi2]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p49_1, u4ehi4]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h1, hlam, p49_1]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h5, hlam, p49_1]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [hlam, p49_0]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h8, hlam, p49_1]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p49_1, u4ehi4]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h2, hlam, p49_1]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h6, hlam, p49_1]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h2, hc03, hlam, hphi, ht0b, ht45, ht5b, p49_1, u4ehi2]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [hlam, p49_0]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h6, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p49_1, u4ehi4]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h4, hlam, p49_0]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h7, hlam, p49_0]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h47, hlam, p49_0]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [h48, hlam, p49_0]
                          · obtain ⟨p49_0, p49_1, p49_2, p49_3⟩ := h49c
                            linarith only [hlam, p49_0]
                        · linarith only [h1, h47, h48, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h47, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h83 | h83
                      · linarith only [h5, h7, h83, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h85 | h85
                        · linarith only [h5, h7, h81, h85, hlam]
                        · rcases h4bigk with h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [hlam, p87_0]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            rcases p87_3 (m.d 0 4) (by simp) with h89 | h89
                            · rcases p87_3 (m.d 1 4) (by simp) with h90 | h90
                              · linarith only [h0, h90, hlam]
                              · rcases p87_3 (m.d 2 4) (by simp) with h92 | h92
                                · linarith only [h1, h92, hlam]
                                · rcases p87_3 (m.d 3 4) (by simp) with h94 | h94
                                  · linarith only [h2, h94, hlam]
                                  · rcases p87_3 (m.d 4 5) (by simp) with h96 | h96
                                    · linarith only [h4, h96, hlam]
                                    · linarith only [h7, h96, hlam]
                            · linarith only [h0, h89, hlam]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            rcases p87_3 (m.d 0 4) (by simp) with h100 | h100
                            · rcases p87_3 (m.d 1 4) (by simp) with h101 | h101
                              · linarith only [h0, h101, hlam]
                              · linarith only [h101, h5, hlam]
                            · linarith only [h1, h100, hlam]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            rcases p87_3 (m.d 0 4) (by simp) with h105 | h105
                            · rcases p87_3 (m.d 1 4) (by simp) with h106 | h106
                              · linarith only [h0, h106, hlam]
                              · linarith only [h106, h6, hlam]
                            · linarith only [h105, h2, hlam]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p87_1, u4ehi1]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [h0, hlam, p87_0]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [hlam, p87_0]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [h7, h81, hc45, hlam, hphi, p87_1, u4ehi3]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p87_1, u3ehi3]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [h7, hlam, p87_0]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [h1, hlam, p87_1]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [h5, hlam, p87_1]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [hlam, p87_0]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p87_1, u3ehi3]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [h83, hlam, p87_0]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [h2, hlam, p87_1]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [h6, hlam, p87_1]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [h81, hlam, p87_0]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [hlam, p87_0]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [h85, hlam, p87_0]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [h4, hlam, p87_0]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p87_1, u4ehi1]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [h0, h4, h81, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p87_1, u3ehi3]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p87_1, u3ehi3]
                          · obtain ⟨p87_0, p87_1, p87_2, p87_3⟩ := h87c
                            linarith only [hlam, p87_0]
                    · linarith only [h81, h82, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h0, h4, h6, h7, h81, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h133 | h133
                · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
                  · linarith only [h134, h5, h6, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h136 | h136
                    · linarith only [h134, h136, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h138 | h138
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h139 | h139
                        · rcases h4bigk with h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [hlam, p140_0]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h0, h138, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p140_1, u4ehi4]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h0, h138, hc01, hlam, hphi, ht0b, ht45, ht5b, p140_1, u4ehi4]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p140_1, u3ehi1]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            rcases p140_3 (m.d 0 4) (by simp) with h145 | h145
                            · rcases p140_3 (m.d 1 4) (by simp) with h146 | h146
                              · linarith only [h0, h146, hlam]
                              · linarith only [h133, h146, hlam]
                            · linarith only [h145, hlam, p140_0]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h0, hlam, p140_0]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [hlam, p140_0]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h138, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p140_1, u4ehi4]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h6, hlam, p140_0]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h2, h6, hc03, hlam, hphi, ht0b, ht45, ht5b, p140_1, u4ehi4]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h1, hlam, p140_1]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h5, hlam, p140_1]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [hlam, p140_0]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h134, hlam, p140_1]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p140_1, u4ehi4]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h2, hlam, p140_1]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h2, hc03, hlam, hphi, ht0b, ht45, ht5b, p140_1, u4ehi1]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h2, hc03, hlam, hphi, ht0b, ht45, ht5b, p140_1, u4ehi2]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [hlam, p140_0]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h2, hc03, hlam, hphi, ht0b, ht45, ht5b, p140_1, u4ehi4]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h4, hlam, p140_0]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h133, hlam, p140_0]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h138, hlam, p140_0]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [h139, hlam, p140_0]
                          · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                            linarith only [hlam, p140_0]
                        · linarith only [h1, h138, h139, h6, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                      · linarith only [h0, h133, h138, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                  · linarith only [h0, h133, h172, h4, h5, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h174 | h174
                    · linarith only [h172, h174, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h176 | h176
                      · linarith only [h133, h176, h5, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h178 | h178
                        · linarith only [h133, h178, h2, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                        · linarith only [h178, h6, hc45, hlam, hphi, ht34, u3ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h181 | h181
              · rcases m.htr 1 4 5 (by decide) (by decide) with h182 | h182
                · rcases m.htr 2 3 4 (by decide) (by decide) with h183 | h183
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h184 | h184
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h185 | h185
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h186 | h186
                        · rcases h4bigk with h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [hlam, p187_0]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h0, h182, hc01, hlam, hphi, ht0b, ht45, ht5b, p187_1, u4ehi4]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h0, h182, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p187_1, u4ehi4]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h0, h186, hc01, hlam, hphi, ht0b, ht45, ht5b, p187_1, u4ehi4]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            rcases p187_3 (m.d 0 4) (by simp) with h192 | h192
                            · rcases p187_3 (m.d 1 4) (by simp) with h193 | h193
                              · linarith only [h0, h193, hlam]
                              · linarith only [h182, h193, hlam]
                            · linarith only [h192, hlam, p187_0]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h0, hlam, p187_0]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [hlam, p187_0]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h5, hlam, p187_0]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h186, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p187_1, u4ehi4]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h1, h5, hc02, hlam, hphi, ht0b, ht45, ht5b, p187_1, u4ehi4]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h1, hlam, p187_1]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p187_1, u4ehi1]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [hlam, p187_0]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h1, h186, hc02, hlam, hphi, ht0b, ht45, ht5b, p187_1, u4ehi4]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p187_1, u4ehi4]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h2, hlam, p187_1]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h181, hlam, p187_1]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h183, hlam, p187_0]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [hlam, p187_0]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h181, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p187_1, u4ehi4]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h4, hlam, p187_0]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h182, hlam, p187_0]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h185, hlam, p187_0]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [h186, hlam, p187_0]
                          · obtain ⟨p187_0, p187_1, p187_2, p187_3⟩ := h187c
                            linarith only [hlam, p187_0]
                        · linarith only [h0, h182, h186, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h182, h185, h5, hlam]
                    · linarith only [h183, h184, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h181, h183, h5, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h221 | h221
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h222 | h222
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h223 | h223
                      · linarith only [h1, h181, h182, h223, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h225 | h225
                        · linarith only [h223, h225, h5, hc12, hc34, hlam, hphi, ht23]
                        · rcases h4bigk with h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [hlam, p227_0]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            rcases p227_3 (m.d 0 4) (by simp) with h229 | h229
                            · rcases p227_3 (m.d 1 4) (by simp) with h230 | h230
                              · linarith only [h0, h230, hlam]
                              · rcases p227_3 (m.d 2 4) (by simp) with h232 | h232
                                · linarith only [h1, h232, hlam]
                                · linarith only [h232, h5, hlam]
                            · linarith only [h0, h229, hlam]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            rcases p227_3 (m.d 0 4) (by simp) with h236 | h236
                            · rcases p227_3 (m.d 1 4) (by simp) with h237 | h237
                              · linarith only [h0, h237, hlam]
                              · rcases p227_3 (m.d 2 4) (by simp) with h239 | h239
                                · linarith only [h1, h239, hlam]
                                · rcases p227_3 (m.d 3 4) (by simp) with h241 | h241
                                  · linarith only [h2, h241, hlam]
                                  · rcases p227_3 (m.d 4 5) (by simp) with h243 | h243
                                    · linarith only [h243, h4, hlam]
                                    · linarith only [h223, h243, hlam]
                            · linarith only [h1, h236, hlam]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            rcases p227_3 (m.d 0 4) (by simp) with h247 | h247
                            · rcases p227_3 (m.d 1 4) (by simp) with h248 | h248
                              · linarith only [h0, h248, hlam]
                              · linarith only [h181, h248, hlam]
                            · linarith only [h2, h247, hlam]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [h0, h181, h223, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p227_1, u3ehi3]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [h0, hlam, p227_0]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [hlam, p227_0]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [h5, hlam, p227_0]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [h223, h5, hc45, hlam, hphi, ht34, p227_1, u3ehi3]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [h182, hlam, p227_0]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [h1, hlam, p227_1]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [h223, hc45, hlam, hphi, p227_1, u4ehi1]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [hlam, p227_0]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [h0, h223, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p227_1, u3ehi3]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [h223, hlam, p227_0]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [h2, hlam, p227_1]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [h181, hlam, p227_1]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [h221, hlam, p227_0]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [hlam, p227_0]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [h225, hlam, p227_0]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [h4, hlam, p227_0]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p227_1, u4ehi1]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [h0, h4, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p227_1]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p227_1, u3ehi3]
                          · obtain ⟨p227_0, p227_1, p227_2, p227_3⟩ := h227c
                            linarith only [hlam, p227_0]
                    · linarith only [h221, h222, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h0, h181, h182, h221, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h275 | h275
                · rcases m.htr 2 3 4 (by decide) (by decide) with h276 | h276
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h277 | h277
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h278 | h278
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h279 | h279
                        · rcases h4bigk with h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [hlam, p280_0]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h0, h275, hc01, hlam, hphi, ht0b, ht45, ht5b, p280_1, u4ehi4]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h0, h181, h276, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p280_1, u3ehi1]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h0, h181, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p280_1, u3ehi1]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            rcases p280_3 (m.d 0 4) (by simp) with h285 | h285
                            · rcases p280_3 (m.d 1 4) (by simp) with h286 | h286
                              · linarith only [h0, h286, hlam]
                              · linarith only [h275, h286, hlam]
                            · linarith only [h285, hlam, p280_0]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h0, hlam, p280_0]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [hlam, p280_0]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h5, hlam, p280_0]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h181, hlam, p280_0]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p280_1, u4ehi4]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h1, hlam, p280_1]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p280_1, u4ehi1]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [hlam, p280_0]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p280_1, u4ehi3]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p280_1, u4ehi4]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h2, hlam, p280_1]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h275, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p280_1, u4ehi4]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h276, hlam, p280_0]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [hlam, p280_0]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h276, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p280_1, u4ehi4]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h4, hlam, p280_0]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h275, hlam, p280_0]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h278, hlam, p280_0]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [h279, hlam, p280_0]
                          · obtain ⟨p280_0, p280_1, p280_2, p280_3⟩ := h280c
                            linarith only [hlam, p280_0]
                        · linarith only [h0, h275, h279, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h181, h275, h276, h278, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h181, h275, h276, h277, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h313 | h313
                    · linarith only [h276, h313, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h315 | h315
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h316 | h316
                        · rcases h4bigk with h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [hlam, p317_0]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h0, h275, hc01, hlam, hphi, ht0b, ht45, ht5b, p317_1, u4ehi4]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h0, h275, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p317_1, u4ehi4]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h0, h181, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p317_1, u3ehi1]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            rcases p317_3 (m.d 0 4) (by simp) with h322 | h322
                            · rcases p317_3 (m.d 1 4) (by simp) with h323 | h323
                              · linarith only [h0, h323, hlam]
                              · linarith only [h275, h323, hlam]
                            · linarith only [h322, hlam, p317_0]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h0, hlam, p317_0]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [hlam, p317_0]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h5, hlam, p317_0]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h181, hlam, p317_0]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p317_1, u4ehi4]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h1, hlam, p317_1]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p317_1, u4ehi1]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [hlam, p317_0]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h276, hlam, p317_1]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h2, h276, hc03, hlam, hphi, ht0b, ht45, ht5b, p317_1, u4ehi4]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h2, hlam, p317_1]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h2, h275, hc03, hlam, hphi, ht0b, ht45, ht5b, p317_1, u4ehi4]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h2, hc03, hlam, hphi, ht0b, ht45, ht5b, p317_1, u4ehi2]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [hlam, p317_0]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h2, hc03, hlam, hphi, ht0b, ht45, ht5b, p317_1, u4ehi4]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h4, hlam, p317_0]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h275, hlam, p317_0]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h315, hlam, p317_0]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [h316, hlam, p317_0]
                          · obtain ⟨p317_0, p317_1, p317_2, p317_3⟩ := h317c
                            linarith only [hlam, p317_0]
                        · linarith only [h0, h275, h316, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h275, h315, h5, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h349 | h349
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h350 | h350
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h351 | h351
                      · linarith only [h1, h275, h351, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                      · linarith only [h181, h349, h351, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h181, h349, h350, hc35, hlam, hphi, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h355 | h355
                    · linarith only [h349, h355, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h357 | h357
                      · linarith only [h181, h2, h275, h349, h357, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h359 | h359
                        · linarith only [h181, h2, h357, h359, h5, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h181, h359, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h362 | h362
            · rcases m.htr 1 3 4 (by decide) (by decide) with h363 | h363
              · rcases m.htr 1 4 5 (by decide) (by decide) with h364 | h364
                · linarith only [h0, h364, h4, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h366 | h366
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h367 | h367
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h368 | h368
                      · linarith only [h0, h362, h368, h4, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h370 | h370
                        · linarith only [h0, h362, h366, h370, h4, hlam]
                        · rcases h4bigk with h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [hlam, p372_0]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h4, hc45, hlam, hphi, p372_1, u4ehi1]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h366, h4, hc45, hlam, hphi, ht34, p372_1, u3ehi3]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h4, hc45, hlam, hphi, ht34, p372_1, u3ehi3]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h4, hlam, p372_0]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h0, hlam, p372_0]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [hlam, p372_0]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h0, h366, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p372_1, u3ehi3]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h0, h4, hc45, hlam, hphi, ht34, p372_1, u3ehi3]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h364, hlam, p372_0]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h1, hlam, p372_1]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h362, hlam, p372_1]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [hlam, p372_0]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h362, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p372_1, u3ehi3]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h368, hlam, p372_0]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h2, hlam, p372_1]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h363, hlam, p372_1]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h366, hlam, p372_0]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [hlam, p372_0]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h370, hlam, p372_0]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [hc45, hlam, hphi, p372_1, u4ehi0]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h363, hc45, hlam, hphi, ht34, p372_1, u3ehi3]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [h366, hc45, hlam, hphi, ht34, p372_1, u3ehi3]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [hc45, hlam, hphi, ht34, p372_1, u3ehi3]
                          · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                            linarith only [hlam, p372_0]
                    · linarith only [h366, h367, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h2, h366, h4, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h2, h363, h4, hc45, hlam, hphi, ht34, u3ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h401 | h401
              · rcases m.htr 1 4 5 (by decide) (by decide) with h402 | h402
                · linarith only [h0, h4, h402, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h404 | h404
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h405 | h405
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h406 | h406
                      · linarith only [h1, h4, h406, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h408 | h408
                        · linarith only [h1, h362, h4, h401, h408, hlam]
                        · rcases h4bigk with h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [hlam, p410_0]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h4, h401, hc45, hlam, hphi, ht34, p410_1, u3ehi3]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h362, h4, h401, hc45, hlam, hphi, ht34, p410_1, u3ehi3]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h4, hc45, hlam, hphi, ht34, p410_1, u3ehi3]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h4, hlam, p410_0]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h0, hlam, p410_0]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [hlam, p410_0]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h362, hlam, p410_0]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p410_1, u3ehi3]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h402, hlam, p410_0]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h1, hlam, p410_1]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p410_1, u4ehi1]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [hlam, p410_0]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h1, h4, hc45, hlam, hphi, ht34, p410_1, u3ehi3]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h406, hlam, p410_0]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h2, hlam, p410_1]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h401, hlam, p410_1]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h404, hlam, p410_0]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [hlam, p410_0]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h408, hlam, p410_0]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [hc45, hlam, hphi, p410_1, u4ehi0]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h401, hc45, hlam, hphi, ht34, p410_1, u3ehi3]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [h362, hc12, hc45, hlam, hphi, ht23, ht34, p410_1]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [hc45, hlam, hphi, ht34, p410_1, u3ehi3]
                          · obtain ⟨p410_0, p410_1, p410_2, p410_3⟩ := h410c
                            linarith only [hlam, p410_0]
                    · linarith only [h404, h405, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h362, h4, h401, h404, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h2, h4, h401, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h2, h3, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h440 | h440
        · linarith only [h2, h440, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h442 | h442
          · rcases m.htr 1 2 4 (by decide) (by decide) with h443 | h443
            · rcases m.htr 1 3 4 (by decide) (by decide) with h444 | h444
              · linarith only [h0, h2, h444, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h446 | h446
                · rcases m.htr 2 3 4 (by decide) (by decide) with h447 | h447
                  · linarith only [h0, h2, h443, h447, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h449 | h449
                    · linarith only [h447, h449, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h451 | h451
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h452 | h452
                        · rcases h4bigk with h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [hlam, p453_0]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h2, h444, hc34, hlam, hphi, p453_1, u3ehi1]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h2, h447, hc34, hlam, hphi, p453_1, u3ehi2]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h2, hlam, p453_0]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            rcases p453_3 (m.d 0 4) (by simp) with h458 | h458
                            · rcases p453_3 (m.d 1 4) (by simp) with h459 | h459
                              · linarith only [h0, h459, hlam]
                              · linarith only [h446, h459, hlam]
                            · linarith only [h458, hlam, p453_0]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h0, hlam, p453_0]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [hlam, p453_0]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h451, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p453_1, u4ehi4]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h444, hlam, p453_0]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p453_1, u4ehi4]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h1, hlam, p453_1]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h443, hlam, p453_1]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [hlam, p453_0]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h447, hlam, p453_1]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h443, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p453_1, u4ehi4]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h2, hc34, hlam, hphi, p453_1, u3ehi0]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h444, hc34, hlam, hphi, p453_1, u3ehi1]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h447, hc34, hlam, hphi, p453_1, u3ehi2]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [hlam, p453_0]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            rcases p453_3 (m.d 0 4) (by simp) with h477 | h477
                            · linarith only [h2, h477, hlam]
                            · linarith only [h442, h477, hlam]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h442, hlam, p453_0]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h446, hlam, p453_0]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h451, hlam, p453_0]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [h452, hlam, p453_0]
                          · obtain ⟨p453_0, p453_1, p453_2, p453_3⟩ := h453c
                            linarith only [hlam, p453_0]
                        · linarith only [h0, h443, h451, h452, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h446, h451, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h2, h442, h444, h446, hc34, hlam, hphi, u3ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h488 | h488
              · linarith only [h0, h2, h488, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h490 | h490
                · rcases m.htr 2 3 4 (by decide) (by decide) with h491 | h491
                  · linarith only [h1, h2, h491, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h493 | h493
                    · linarith only [h440, h491, h493, hc34, hlam, hphi, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h495 | h495
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h496 | h496
                        · rcases h4bigk with h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [hlam, p497_0]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h490, hc04, hlam, hphi, ht0b, ht45, ht5b, p497_1, u4ehi4]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h2, h443, hc12, hc34, hlam, hphi, ht23, p497_1]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h2, hlam, p497_0]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            rcases p497_3 (m.d 0 4) (by simp) with h502 | h502
                            · rcases p497_3 (m.d 1 4) (by simp) with h503 | h503
                              · linarith only [h0, h503, hlam]
                              · linarith only [h490, h503, hlam]
                            · linarith only [h502, hlam, p497_0]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h0, hlam, p497_0]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [hlam, p497_0]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h443, hlam, p497_0]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h488, hlam, p497_0]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p497_1, u4ehi4]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h1, hlam, p497_1]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h1, h488, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p497_1, u3ehi1]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [hlam, p497_0]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h491, hlam, p497_1]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p497_1, u4ehi4]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h0, h490, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p497_1, u4ehi4]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h490, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p497_1, u4ehi4]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h443, h490, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p497_1, u4ehi4]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [hlam, p497_0]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            rcases p497_3 (m.d 0 4) (by simp) with h521 | h521
                            · linarith only [h2, h521, hlam]
                            · linarith only [h442, h521, hlam]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h442, hlam, p497_0]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h490, hlam, p497_0]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h495, hlam, p497_0]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [h496, hlam, p497_0]
                          · obtain ⟨p497_0, p497_1, p497_2, p497_3⟩ := h497c
                            linarith only [hlam, p497_0]
                        · linarith only [h0, h490, h496, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h443, h490, h495, hlam]
                · linarith only [h2, h442, h488, h490, hc34, hlam, hphi, u3ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h532 | h532
            · rcases m.htr 1 3 4 (by decide) (by decide) with h533 | h533
              · linarith only [h0, h2, h442, h533, hc45, hlam, hphi, ht34, u3ehi0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h535 | h535
                · linarith only [h0, h442, h535, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h537 | h537
                  · linarith only [h0, h2, h442, h532, h537, hc45, hlam, hphi, ht34, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h539 | h539
                    · linarith only [h537, h539, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h541 | h541
                      · linarith only [h0, h442, h532, h541, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h543 | h543
                        · linarith only [h0, h442, h533, h543, hc34, hlam, hphi, u3ehi1]
                        · linarith only [h2, h543, hc45, hlam, hphi, ht34, u3ehi0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h546 | h546
              · linarith only [h1, h2, h532, h546, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h548 | h548
                · linarith only [h1, h442, h532, h548, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h550 | h550
                  · linarith only [h1, h2, h442, h550, hc45, hlam, hphi, ht34, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h552 | h552
                    · linarith only [h440, h550, h552, hc34, hlam, hphi, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h554 | h554
                      · linarith only [h1, h442, h554, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h556 | h556
                        · linarith only [h1, h442, h532, h556, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h2, h556, hc45, hlam, hphi, ht34, u3ehi0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h559 | h559
      · rcases m.htr 0 3 5 (by decide) (by decide) with h560 | h560
        · rcases m.htr 0 4 5 (by decide) (by decide) with h561 | h561
          · rcases m.htr 1 2 4 (by decide) (by decide) with h562 | h562
            · linarith only [h0, h1, h562, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h564 | h564
              · rcases m.htr 1 4 5 (by decide) (by decide) with h565 | h565
                · rcases m.htr 2 3 4 (by decide) (by decide) with h566 | h566
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h567 | h567
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h568 | h568
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h569 | h569
                        · rcases h4bigk with h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [hlam, p570_0]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h564, h569, hc04, hlam, hphi, ht0b, ht45, ht5b, p570_1, u4ehi4]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h1, hlam, p570_0]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h1, h569, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p570_1, u4ehi4]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            rcases p570_3 (m.d 0 4) (by simp) with h575 | h575
                            · rcases p570_3 (m.d 1 4) (by simp) with h576 | h576
                              · linarith only [h0, h576, hlam]
                              · linarith only [h565, h576, hlam]
                            · linarith only [h575, hlam, p570_0]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h0, hlam, p570_0]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [hlam, p570_0]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h562, hlam, p570_0]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h569, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p570_1, u4ehi4]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p570_1, u4ehi4]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h559, h566, h569, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p570_1, u4ehi4]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h564, h566, h569, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p570_1, u4ehi4]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [hlam, p570_0]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h566, h569, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p570_1, u4ehi4]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            rcases p570_3 (m.d 0 4) (by simp) with h589 | h589
                            · linarith only [h1, h589, hlam]
                            · linarith only [h561, h589, hlam]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h559, hlam, p570_1]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h564, hlam, p570_1]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h566, hlam, p570_0]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [hlam, p570_0]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h559, hc03, hlam, hphi, ht0b, ht45, ht5b, p570_1, u4ehi4]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h561, hlam, p570_0]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h565, hlam, p570_0]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h568, hlam, p570_0]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [h569, hlam, p570_0]
                          · obtain ⟨p570_0, p570_1, p570_2, p570_3⟩ := h570c
                            linarith only [hlam, p570_0]
                        · linarith only [h0, h565, h569, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h1, h565, h568, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h566, h567, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h559, h566, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h606 | h606
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h607 | h607
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h608 | h608
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h609 | h609
                        · linarith only [h564, h565, h609, hlam]
                        · rcases h4bigk with h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [hlam, p611_0]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            rcases p611_3 (m.d 0 4) (by simp) with h613 | h613
                            · rcases p611_3 (m.d 1 4) (by simp) with h614 | h614
                              · linarith only [h0, h614, hlam]
                              · rcases p611_3 (m.d 2 4) (by simp) with h616 | h616
                                · rcases p611_3 (m.d 3 4) (by simp) with h617 | h617
                                  · linarith only [h559, h617, hlam]
                                  · rcases p611_3 (m.d 4 5) (by simp) with h619 | h619
                                    · linarith only [h561, h619, hlam]
                                    · linarith only [h565, h619, hlam]
                                · linarith only [h562, h616, hlam]
                            · linarith only [h0, h613, hlam]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [h1, hlam, p611_0]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            rcases p611_3 (m.d 0 4) (by simp) with h625 | h625
                            · rcases p611_3 (m.d 1 4) (by simp) with h626 | h626
                              · linarith only [h0, h626, hlam]
                              · linarith only [h564, h626, hlam]
                            · linarith only [h559, h625, hlam]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [h1, h564, h565, h606, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p611_1, u3ehi3]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [h0, hlam, p611_0]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [hlam, p611_0]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [h562, hlam, p611_0]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [h565, h608, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p611_1, u3ehi3]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [h565, hlam, p611_0]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [h561, h606, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p611_1, u4ehi4]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            rcases p611_3 (m.d 0 4) (by simp) with h637 | h637
                            · linarith only [h1, h637, hlam]
                            · linarith only [h0, h637, hlam]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [hlam, p611_0]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            rcases p611_3 (m.d 0 4) (by simp) with h641 | h641
                            · linarith only [h1, h641, hlam]
                            · linarith only [h559, h641, hlam]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [h564, h565, h606, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p611_1, u3ehi3]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [h559, hlam, p611_1]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [h564, hlam, p611_1]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [h606, hlam, p611_0]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [hlam, p611_0]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [h609, hlam, p611_0]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [h561, hlam, p611_0]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [h561, h564, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p611_1, u3ehi3]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [h608, hlam, p611_0]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [h1, h561, h606, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p611_1, u3ehi3]
                          · obtain ⟨p611_0, p611_1, p611_2, p611_3⟩ := h611c
                            linarith only [hlam, p611_0]
                      · linarith only [h1, h561, h608, hlam]
                    · linarith only [h1, h560, h561, h606, h607, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h1, h561, h564, h565, h606, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h658 | h658
                · rcases m.htr 2 3 4 (by decide) (by decide) with h659 | h659
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h660 | h660
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h661 | h661
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h662 | h662
                        · rcases h4bigk with h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [hlam, p663_0]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h1, h658, h659, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p663_1, u4ehi4]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h1, hlam, p663_0]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h1, h564, h659, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p663_1, u3ehi1]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            rcases p663_3 (m.d 0 4) (by simp) with h668 | h668
                            · rcases p663_3 (m.d 1 4) (by simp) with h669 | h669
                              · linarith only [h0, h669, hlam]
                              · linarith only [h658, h669, hlam]
                            · linarith only [h668, hlam, p663_0]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h0, hlam, p663_0]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [hlam, p663_0]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h562, hlam, p663_0]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h564, hlam, p663_0]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p663_1, u4ehi4]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h559, h564, h659, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p663_1, u3ehi1]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h658, h659, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p663_1, u4ehi4]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [hlam, p663_0]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h564, h659, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p663_1, u3ehi1]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            rcases p663_3 (m.d 0 4) (by simp) with h682 | h682
                            · linarith only [h1, h682, hlam]
                            · linarith only [h561, h682, hlam]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h559, hlam, p663_1]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h559, h658, hc04, hlam, hphi, ht0b, ht45, ht5b, p663_1, u4ehi4]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h659, hlam, p663_0]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [hlam, p663_0]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h659, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p663_1, u4ehi4]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h561, hlam, p663_0]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h658, hlam, p663_0]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h661, hlam, p663_0]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [h662, hlam, p663_0]
                          · obtain ⟨p663_0, p663_1, p663_2, p663_3⟩ := h663c
                            linarith only [hlam, p663_0]
                        · linarith only [h0, h658, h662, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1, h564, h658, h659, h661, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · linarith only [h560, h561, h564, h659, h660, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h1, h559, h659, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h699 | h699
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h700 | h700
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h701 | h701
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h702 | h702
                        · linarith only [h564, h658, h699, h702, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h561, h564, h702, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h1, h561, h701, hlam]
                    · linarith only [h1, h559, h564, h699, h700, hc35, hlam, hphi, u3ehi1]
                  · linarith only [h1, h561, h564, h658, h699, hc34, hlam, hphi, u3ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h708 | h708
            · linarith only [h0, h1, h708, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h710 | h710
              · rcases m.htr 1 4 5 (by decide) (by decide) with h711 | h711
                · linarith only [h0, h561, h711, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h713 | h713
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h714 | h714
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h715 | h715
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h716 | h716
                        · linarith only [h0, h561, h710, h716, hlam]
                        · rcases h4bigk with h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [hlam, p718_0]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [h561, h710, h713, h715, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p718_1, u3ehi3]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [h1, hlam, p718_0]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [h561, h713, h715, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p718_1, u3ehi3]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [h561, hlam, p718_0]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [h0, hlam, p718_0]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [hlam, p718_0]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [h708, hlam, p718_0]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p718_1, u3ehi3]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [h711, hlam, p718_0]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            rcases p718_3 (m.d 0 4) (by simp) with h729 | h729
                            · linarith only [h1, h729, hlam]
                            · rcases p718_3 (m.d 1 4) (by simp) with h731 | h731
                              · linarith only [h708, h731, hlam]
                              · rcases p718_3 (m.d 2 4) (by simp) with h733 | h733
                                · rcases p718_3 (m.d 3 4) (by simp) with h734 | h734
                                  · linarith only [h713, h734, hlam]
                                  · rcases p718_3 (m.d 4 5) (by simp) with h736 | h736
                                    · linarith only [h715, h736, hlam]
                                    · linarith only [h561, h736, hlam]
                                · linarith only [h1, h733, hlam]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            rcases p718_3 (m.d 0 4) (by simp) with h740 | h740
                            · linarith only [h1, h740, hlam]
                            · linarith only [h0, h740, hlam]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [hlam, p718_0]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            rcases p718_3 (m.d 0 4) (by simp) with h744 | h744
                            · linarith only [h1, h744, hlam]
                            · linarith only [h559, h744, hlam]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [h561, h713, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p718_1, u4ehi0]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [h559, hlam, p718_1]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [h710, hlam, p718_1]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [h713, hlam, p718_0]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [hlam, p718_0]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [h716, hlam, p718_0]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [h0, hc45, hlam, hphi, p718_1, u4ehi1]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [h710, hc45, hlam, hphi, ht34, p718_1, u3ehi3]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [h715, hlam, p718_0]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [h713, h715, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p718_1, u3ehi3]
                          · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                            linarith only [hlam, p718_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h758 | h758
                        · linarith only [h1, h710, h715, h758, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h4bigk with h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [hlam, p760_0]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h1, h710, h715, hc45, hlam, hphi, ht34, p760_1, u3ehi3]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h1, hlam, p760_0]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h1, h715, hc45, hlam, hphi, ht34, p760_1, u3ehi3]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h561, hlam, p760_0]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h0, hlam, p760_0]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [hlam, p760_0]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h708, hlam, p760_0]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p760_1, u3ehi3]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h711, hlam, p760_0]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h715, hc45, hlam, hphi, p760_1, u4ehi0]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h715, hc45, hlam, hphi, p760_1, u4ehi1]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [hlam, p760_0]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h715, hc45, hlam, hphi, ht34, p760_1, u3ehi3]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h715, hlam, p760_0]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h559, hlam, p760_1]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h710, hlam, p760_1]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h713, hlam, p760_0]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [hlam, p760_0]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h758, hlam, p760_0]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [hc45, hlam, hphi, p760_1, u4ehi0]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h710, hc45, hlam, hphi, ht34, p760_1, u3ehi3]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p760_1]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [hc45, hlam, hphi, ht34, p760_1, u3ehi3]
                          · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                            linarith only [hlam, p760_0]
                    · linarith only [h713, h714, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h0, h561, h710, h713, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h559, h561, h710, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h559, h560, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h790 | h790
        · linarith only [h559, h790, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h792 | h792
          · rcases m.htr 1 2 4 (by decide) (by decide) with h793 | h793
            · linarith only [h0, h1, h793, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h795 | h795
              · linarith only [h0, h559, h795, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h797 | h797
                · rcases m.htr 2 3 4 (by decide) (by decide) with h798 | h798
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h799 | h799
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h800 | h800
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h801 | h801
                        · rcases h4bigk with h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [hlam, p802_0]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h559, h798, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p802_1, u4ehi1]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h1, hlam, p802_0]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h559, hlam, p802_0]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h559, h798, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p802_1, u4ehi4]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h0, hlam, p802_0]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [hlam, p802_0]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h793, hlam, p802_0]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h795, hlam, p802_0]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p802_1, u4ehi4]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h792, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p802_1, u4ehi4]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h797, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p802_1, u4ehi4]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [hlam, p802_0]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h0, h559, h797, h798, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p802_1, u4ehi4]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            rcases p802_3 (m.d 0 4) (by simp) with h817 | h817
                            · linarith only [h1, h817, hlam]
                            · linarith only [h792, h817, hlam]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h0, h797, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p802_1, u4ehi4]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h797, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p802_1, u4ehi4]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h798, hlam, p802_0]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [hlam, p802_0]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h798, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p802_1, u4ehi4]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h792, hlam, p802_0]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h797, hlam, p802_0]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h800, hlam, p802_0]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [h801, hlam, p802_0]
                          · obtain ⟨p802_0, p802_1, p802_2, p802_3⟩ := h802c
                            linarith only [hlam, p802_0]
                        · linarith only [h0, h797, h801, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h559, h797, h798, h800, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h559, h797, h798, h799, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h833 | h833
                    · linarith only [h798, h833, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h835 | h835
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h836 | h836
                        · rcases h4bigk with h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [hlam, p837_0]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [h1, h797, h798, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p837_1, u4ehi4]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [h1, hlam, p837_0]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [h559, hlam, p837_0]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            rcases p837_3 (m.d 0 4) (by simp) with h842 | h842
                            · rcases p837_3 (m.d 1 4) (by simp) with h843 | h843
                              · linarith only [h0, h843, hlam]
                              · linarith only [h797, h843, hlam]
                            · linarith only [h842, hlam, p837_0]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [h0, hlam, p837_0]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [hlam, p837_0]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [h793, hlam, p837_0]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [h795, hlam, p837_0]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p837_1, u4ehi4]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [h559, h798, hc34, hlam, hphi, p837_1, u3ehi0]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [h795, h798, hc34, hlam, hphi, p837_1, u3ehi1]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [hlam, p837_0]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [h798, hlam, p837_1]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            rcases p837_3 (m.d 0 4) (by simp) with h856 | h856
                            · linarith only [h1, h856, hlam]
                            · linarith only [h792, h856, hlam]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [h0, h797, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p837_1, u4ehi4]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [h797, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p837_1, u4ehi4]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [h1, hc02, hc34, hlam, hphi, ht23, p837_1]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [hlam, p837_0]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            rcases p837_3 (m.d 0 4) (by simp) with h863 | h863
                            · linarith only [h559, h863, hlam]
                            · linarith only [h792, h863, hlam]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [h792, hlam, p837_0]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [h797, hlam, p837_0]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [h835, hlam, p837_0]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [h836, hlam, p837_0]
                          · obtain ⟨p837_0, p837_1, p837_2, p837_3⟩ := h837c
                            linarith only [hlam, p837_0]
                        · linarith only [h0, h797, h836, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h1, h797, h835, hlam]
                · linarith only [h559, h792, h795, h797, hc34, hlam, hphi, u3ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h874 | h874
            · linarith only [h0, h1, h874, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h876 | h876
              · linarith only [h0, h559, h792, h876, hc45, hlam, hphi, ht34, u3ehi0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h878 | h878
                · linarith only [h0, h792, h878, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h880 | h880
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h881 | h881
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h882 | h882
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h883 | h883
                        · linarith only [h0, h792, h876, h883, hc34, hlam, hphi, u3ehi1]
                        · linarith only [h559, h880, h882, h883, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h559, h880, h882, hc45, hlam, hphi, ht34, u3ehi0]
                    · linarith only [h559, h880, h881, hc35, hlam, hphi, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h888 | h888
                    · linarith only [h880, h888, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h890 | h890
                      · linarith only [h0, h792, h876, h880, h890, hc34, hlam, hphi, u3ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h892 | h892
                        · linarith only [h1, h890, h892, hc02, hc34, hlam, hphi, ht23]
                        · linarith only [h559, h892, hc45, hlam, hphi, ht34, u3ehi0]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h895 | h895
    · rcases m.htr 0 3 4 (by decide) (by decide) with h896 | h896
      · rcases m.htr 0 3 5 (by decide) (by decide) with h897 | h897
        · rcases m.htr 0 4 5 (by decide) (by decide) with h898 | h898
          · rcases m.htr 1 2 4 (by decide) (by decide) with h899 | h899
            · rcases m.htr 1 3 4 (by decide) (by decide) with h900 | h900
              · rcases m.htr 1 4 5 (by decide) (by decide) with h901 | h901
                · rcases m.htr 2 3 4 (by decide) (by decide) with h902 | h902
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h903 | h903
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h904 | h904
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h905 | h905
                        · rcases h4bigk with h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [hlam, p906_0]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h0, hlam, p906_1]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h902, h905, hc04, hlam, hphi, ht0b, ht45, ht5b, p906_1, u4ehi4]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h0, h899, h905, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p906_1, u4ehi4]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            rcases p906_3 (m.d 0 4) (by simp) with h911 | h911
                            · rcases p906_3 (m.d 1 4) (by simp) with h912 | h912
                              · rcases p906_3 (m.d 2 4) (by simp) with h913 | h913
                                · linarith only [h895, h913, hlam]
                                · linarith only [h904, h913, hlam]
                              · linarith only [h901, h912, hlam]
                            · linarith only [h911, hlam, p906_0]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h895, h899, h902, h905, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p906_1, u4ehi4]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [hlam, p906_0]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h899, h902, h905, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p906_1, u4ehi4]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h899, h905, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p906_1, u4ehi4]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            rcases p906_3 (m.d 0 4) (by simp) with h922 | h922
                            · linarith only [h0, h922, hlam]
                            · linarith only [h898, h922, hlam]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h895, hlam, p906_1]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h899, hlam, p906_1]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [hlam, p906_0]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h895, h905, hc02, hlam, hphi, ht0b, ht45, ht5b, p906_1, u4ehi4]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h899, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p906_1, u4ehi4]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h896, hlam, p906_1]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h900, hlam, p906_1]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h902, hlam, p906_0]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [hlam, p906_0]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h896, hc03, hlam, hphi, ht0b, ht45, ht5b, p906_1, u4ehi4]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h898, hlam, p906_0]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h901, hlam, p906_0]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h904, hlam, p906_0]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [h905, hlam, p906_0]
                          · obtain ⟨p906_0, p906_1, p906_2, p906_3⟩ := h906c
                            linarith only [hlam, p906_0]
                        · linarith only [h899, h904, h905, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h941 | h941
                        · linarith only [h902, h904, h941, hlam]
                        · rcases h4bigk with h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [hlam, p943_0]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [h0, hlam, p943_1]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            rcases p943_3 (m.d 0 4) (by simp) with h946 | h946
                            · rcases p943_3 (m.d 1 4) (by simp) with h947 | h947
                              · rcases p943_3 (m.d 2 4) (by simp) with h948 | h948
                                · linarith only [h895, h948, hlam]
                                · rcases p943_3 (m.d 3 4) (by simp) with h950 | h950
                                  · linarith only [h896, h950, hlam]
                                  · rcases p943_3 (m.d 4 5) (by simp) with h952 | h952
                                    · linarith only [h898, h952, hlam]
                                    · linarith only [h904, h952, hlam]
                              · linarith only [h899, h947, hlam]
                            · linarith only [h895, h946, hlam]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            rcases p943_3 (m.d 0 4) (by simp) with h957 | h957
                            · rcases p943_3 (m.d 1 4) (by simp) with h958 | h958
                              · rcases p943_3 (m.d 2 4) (by simp) with h959 | h959
                                · linarith only [h895, h959, hlam]
                                · linarith only [h902, h959, hlam]
                              · linarith only [h900, h958, hlam]
                            · linarith only [h896, h957, hlam]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [h902, h904, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p943_1, u3ehi3]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [h898, h900, h902, h904, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p943_1, u3ehi3]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [hlam, p943_0]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            rcases p943_3 (m.d 0 4) (by simp) with h967 | h967
                            · linarith only [h0, h967, hlam]
                            · linarith only [h895, h967, hlam]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            rcases p943_3 (m.d 0 4) (by simp) with h970 | h970
                            · linarith only [h0, h970, hlam]
                            · linarith only [h896, h970, hlam]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [h900, h902, h904, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p943_1, u3ehi3]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [h895, hlam, p943_1]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [h899, hlam, p943_1]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [hlam, p943_0]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [h898, h904, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p943_1, u3ehi3]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [h904, hlam, p943_0]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [h896, hlam, p943_1]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [h900, hlam, p943_1]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [h902, hlam, p943_0]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [hlam, p943_0]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [h941, hlam, p943_0]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [h898, hlam, p943_0]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [h901, hlam, p943_0]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [h898, hc04, hlam, hphi, ht0b, ht45, ht5b, p943_1, u4ehi2]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [h0, h898, h900, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p943_1, u3ehi3]
                          · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                            linarith only [hlam, p943_0]
                    · linarith only [h902, h903, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h990 | h990
                    · linarith only [h902, h990, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h992 | h992
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h993 | h993
                        · rcases h4bigk with h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [hlam, p994_0]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h0, hlam, p994_1]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h0, h900, h992, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p994_1, u4ehi4]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h0, h900, h902, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p994_1, u3ehi2]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            rcases p994_3 (m.d 0 4) (by simp) with h999 | h999
                            · rcases p994_3 (m.d 1 4) (by simp) with h1000 | h1000
                              · rcases p994_3 (m.d 2 4) (by simp) with h1001 | h1001
                                · linarith only [h1001, h895, hlam]
                                · linarith only [h1001, h992, hlam]
                              · linarith only [h1000, h901, hlam]
                            · linarith only [h999, hlam, p994_0]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h895, h900, h992, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p994_1, u4ehi4]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [hlam, p994_0]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h900, h992, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p994_1, u4ehi4]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h900, h990, h993, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p994_1, u3ehi2]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            rcases p994_3 (m.d 0 4) (by simp) with h1010 | h1010
                            · linarith only [h0, h1010, hlam]
                            · linarith only [h1010, h898, hlam]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h895, hlam, p994_1]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h899, hlam, p994_1]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [hlam, p994_0]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h902, hlam, p994_1]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h895, hc02, hlam, hphi, ht0b, ht45, ht5b, p994_1, u4ehi4]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h896, hlam, p994_1]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h900, hlam, p994_1]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h896, hc03, hlam, hphi, ht0b, ht45, ht5b, p994_1, u4ehi2]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [hlam, p994_0]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h900, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p994_1, u4ehi4]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h898, hlam, p994_0]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h901, hlam, p994_0]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h992, hlam, p994_0]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [h993, hlam, p994_0]
                          · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                            linarith only [hlam, p994_0]
                        · linarith only [h895, h992, h993, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1029 | h1029
                        · linarith only [h1029, h902, h992, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h0, h1029, h898, h900, h902, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h898, h901, hlam]
              · linarith only [h0, h896, h900, hlam]
            · linarith only [h0, h895, h899, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1035 | h1035
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1036 | h1036
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1037 | h1037
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1038 | h1038
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1039 | h1039
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1040 | h1040
                      · linarith only [h1040, h895, h898, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1042 | h1042
                        · linarith only [h1038, h1042, h895, h898, hlam]
                        · rcases h4bigk with h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c | h1044c
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [hlam, p1044_0]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [h0, hlam, p1044_1]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [h1035, h1037, h1038, h898, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1044_1, u3ehi3]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [h1035, h1037, h898, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1044_1, u3ehi3]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [h898, hlam, p1044_0]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            rcases p1044_3 (m.d 0 4) (by simp) with h1050 | h1050
                            · linarith only [h0, h1050, hlam]
                            · rcases p1044_3 (m.d 1 4) (by simp) with h1052 | h1052
                              · rcases p1044_3 (m.d 2 4) (by simp) with h1053 | h1053
                                · linarith only [h1035, h1053, hlam]
                                · rcases p1044_3 (m.d 3 4) (by simp) with h1055 | h1055
                                  · linarith only [h1036, h1055, hlam]
                                  · rcases p1044_3 (m.d 4 5) (by simp) with h1057 | h1057
                                    · linarith only [h1037, h1057, hlam]
                                    · linarith only [h1057, h898, hlam]
                              · linarith only [h0, h1052, hlam]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [hlam, p1044_0]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            rcases p1044_3 (m.d 0 4) (by simp) with h1062 | h1062
                            · linarith only [h0, h1062, hlam]
                            · linarith only [h1062, h895, hlam]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            rcases p1044_3 (m.d 0 4) (by simp) with h1065 | h1065
                            · linarith only [h0, h1065, hlam]
                            · linarith only [h1065, h896, hlam]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [h0, h1035, h898, hc01, hc12, hlam, hphi, p1044_1]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [h895, hlam, p1044_1]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [h1035, hlam, p1044_1]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [hlam, p1044_0]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [h895, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1044_1, u3ehi3]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [h1040, hlam, p1044_0]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [h896, hlam, p1044_1]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [h1036, hlam, p1044_1]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [h1038, hlam, p1044_0]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [hlam, p1044_0]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [h1042, hlam, p1044_0]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [hc45, hlam, hphi, p1044_1, u4ehi0]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [h1037, hlam, p1044_0]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [h1035, h1037, h1038, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1044_1, u3ehi3]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [h1035, h1037, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1044_1, u3ehi3]
                          · obtain ⟨p1044_0, p1044_1, p1044_2, p1044_3⟩ := h1044c
                            linarith only [hlam, p1044_0]
                    · linarith only [h1038, h1039, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1035, h1037, h1038, h896, h898, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1086 | h1086
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1087 | h1087
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1088 | h1088
                      · linarith only [h0, h1037, h1088, h895, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1090 | h1090
                        · linarith only [h0, h1037, h1086, h1090, h895, hlam]
                        · rcases h4bigk with h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [hlam, p1092_0]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h0, hlam, p1092_1]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h0, h1037, h1086, hc45, hlam, hphi, p1092_1, u4ehi3]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h0, h1037, hc45, hlam, hphi, ht34, p1092_1, u3ehi3]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h898, hlam, p1092_0]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h1037, hc45, hlam, hphi, p1092_1, u4ehi0]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [hlam, p1092_0]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h1037, h1086, hc45, hlam, hphi, ht34, p1092_1, u3ehi3]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h1037, hc45, hlam, hphi, ht34, p1092_1, u3ehi3]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h1037, hlam, p1092_0]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h895, hlam, p1092_1]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h1035, hlam, p1092_1]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [hlam, p1092_0]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h0, h1037, h895, hc45, hlam, hphi, ht34, p1092_1, u3ehi3]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h1088, hlam, p1092_0]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h896, hlam, p1092_1]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h1036, hlam, p1092_1]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h1086, hlam, p1092_0]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [hlam, p1092_0]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h1090, hlam, p1092_0]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [hc45, hlam, hphi, p1092_1, u4ehi0]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1092_1]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [h1086, hc45, hlam, hphi, ht34, p1092_1, u3ehi3]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [hc45, hlam, hphi, ht34, p1092_1, u3ehi3]
                          · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                            linarith only [hlam, p1092_0]
                    · linarith only [h1086, h1087, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1086, h896, h898, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h1036, h896, h898, hc45, hlam, hphi, ht34, u3ehi1]
            · linarith only [h0, h1035, h895, hlam]
        · linarith only [h896, h897, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1123 | h1123
        · linarith only [h1123, h896, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1125 | h1125
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1126 | h1126
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1127 | h1127
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1128 | h1128
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1129 | h1129
                  · linarith only [h1129, h895, h896, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1131 | h1131
                    · linarith only [h1123, h1127, h1129, h1131, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1133 | h1133
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1134 | h1134
                        · rcases h4bigk with h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [hlam, p1135_0]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h0, hlam, p1135_1]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h1127, h896, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1135_1, u4ehi2]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h896, hlam, p1135_0]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h1127, h896, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1135_1, u4ehi4]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h1125, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1135_1, u4ehi4]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [hlam, p1135_0]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h1126, h1133, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1135_1, u4ehi4]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h1126, h896, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1135_1, u3ehi0]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            rcases p1135_3 (m.d 0 4) (by simp) with h1145 | h1145
                            · linarith only [h0, h1145, hlam]
                            · linarith only [h1125, h1145, hlam]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h895, hlam, p1135_1]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h1126, hlam, p1135_1]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [hlam, p1135_0]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h1129, hlam, p1135_1]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h895, hc02, hlam, hphi, ht0b, ht45, ht5b, p1135_1, u4ehi4]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h896, hc34, hlam, hphi, p1135_1, u3ehi0]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h1127, hlam, p1135_1]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h1127, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1135_1, u4ehi2]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [hlam, p1135_0]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h1127, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1135_1, u4ehi4]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h1125, hlam, p1135_0]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h1128, hlam, p1135_0]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h1133, hlam, p1135_0]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [h1134, hlam, p1135_0]
                          · obtain ⟨p1135_0, p1135_1, p1135_2, p1135_3⟩ := h1135c
                            linarith only [hlam, p1135_0]
                        · linarith only [h1133, h1134, h895, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1125, h1127, h1133, h896, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h1125, h1127, h1128, h896, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1166 | h1166
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1167 | h1167
                  · linarith only [h0, h1127, h1167, h895, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1169 | h1169
                    · linarith only [h1123, h1167, h1169, hc34, hlam, hphi, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1171 | h1171
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1172 | h1172
                        · rcases h4bigk with h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [hlam, p1173_0]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [h0, hlam, p1173_1]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [h0, h1171, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1173_1, u4ehi4]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [h896, hlam, p1173_0]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            rcases p1173_3 (m.d 0 4) (by simp) with h1178 | h1178
                            · rcases p1173_3 (m.d 1 4) (by simp) with h1179 | h1179
                              · rcases p1173_3 (m.d 2 4) (by simp) with h1180 | h1180
                                · linarith only [h1180, h895, hlam]
                                · linarith only [h1171, h1180, hlam]
                              · linarith only [h1166, h1179, hlam]
                            · linarith only [h1178, hlam, p1173_0]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [h1127, h1171, h895, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1173_1, u4ehi4]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [hlam, p1173_0]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [h1127, h1171, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1173_1, u4ehi4]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [h1127, hlam, p1173_0]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            rcases p1173_3 (m.d 0 4) (by simp) with h1189 | h1189
                            · linarith only [h0, h1189, hlam]
                            · linarith only [h1125, h1189, hlam]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [h895, hlam, p1173_1]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [h1126, hlam, p1173_1]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [hlam, p1173_0]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [h1167, hlam, p1173_1]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [h895, hc02, hlam, hphi, ht0b, ht45, ht5b, p1173_1, u4ehi4]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [h896, hc34, hlam, hphi, p1173_1, u3ehi0]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1173_1]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [h1167, hc34, hlam, hphi, p1173_1, u3ehi2]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [hlam, p1173_0]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            rcases p1173_3 (m.d 0 4) (by simp) with h1201 | h1201
                            · linarith only [h1201, h896, hlam]
                            · linarith only [h1125, h1201, hlam]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [h1125, hlam, p1173_0]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [h1166, hlam, p1173_0]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [h1171, hlam, p1173_0]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [h1172, hlam, p1173_0]
                          · obtain ⟨p1173_0, p1173_1, p1173_2, p1173_3⟩ := h1173c
                            linarith only [hlam, p1173_0]
                        · linarith only [h1171, h1172, h895, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h1125, h1127, h1167, h1171, hc34, hlam, hphi, u3ehi2]
                · linarith only [h0, h1125, h1166, hlam]
            · linarith only [h0, h1126, h895, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1213 | h1213
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1214 | h1214
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1215 | h1215
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1216 | h1216
                  · linarith only [h1125, h1213, h1215, h1216, h895, h896, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1218 | h1218
                    · linarith only [h1123, h1216, h1218, hc34, hlam, hphi, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1220 | h1220
                      · linarith only [h1125, h1220, h895, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1222 | h1222
                        · linarith only [h1125, h1214, h1222, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                        · linarith only [h1222, h896, hc45, hlam, hphi, ht34, u3ehi0]
                · linarith only [h1214, h1215, h896, hc45, hlam, hphi, ht34, u3ehi0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1226 | h1226
                · linarith only [h1125, h1214, h1226, h896, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1228 | h1228
                  · linarith only [h0, h1214, h1226, h1228, h895, hc45, hlam, hphi, ht34, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1230 | h1230
                    · linarith only [h1123, h1228, h1230, hc34, hlam, hphi, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1232 | h1232
                      · linarith only [h0, h1226, h1232, h895, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1234 | h1234
                        · linarith only [h0, h1226, h1234, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1234, h896, hc45, hlam, hphi, ht34, u3ehi0]
            · linarith only [h0, h1213, h895, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1238 | h1238
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1239 | h1239
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1240 | h1240
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1241 | h1241
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1242 | h1242
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1243 | h1243
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1244 | h1244
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1245 | h1245
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1246 | h1246
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1247 | h1247
                        · rcases h4bigk with h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [hlam, p1248_0]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h0, hlam, p1248_1]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h895, hlam, p1248_0]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h1247, hc04, hlam, hphi, ht0b, ht45, ht5b, p1248_1, u4ehi4]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h1241, h895, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1248_1, u4ehi4]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h1238, h1247, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1248_1, u4ehi4]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [hlam, p1248_0]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h1238, h1241, h1247, h895, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1248_1, u4ehi4]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h1241, h1247, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1248_1, u4ehi4]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            rcases p1248_3 (m.d 0 4) (by simp) with h1258 | h1258
                            · linarith only [h0, h1258, hlam]
                            · linarith only [h1240, h1258, hlam]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h1238, h1247, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1248_1, u4ehi4]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h1241, hlam, p1248_1]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [hlam, p1248_0]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h1241, h1247, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1248_1, u4ehi4]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h1241, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1248_1, u4ehi4]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h1238, hlam, p1248_1]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h1242, hlam, p1248_1]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h1244, hlam, p1248_0]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [hlam, p1248_0]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h1238, hc03, hlam, hphi, ht0b, ht45, ht5b, p1248_1, u4ehi4]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h1240, hlam, p1248_0]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h1243, hlam, p1248_0]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h1246, hlam, p1248_0]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [h1247, hlam, p1248_0]
                          · obtain ⟨p1248_0, p1248_1, p1248_2, p1248_3⟩ := h1248c
                            linarith only [hlam, p1248_0]
                        · linarith only [h1240, h1241, h1247, h895, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h1240, h1246, h895, hlam]
                    · linarith only [h1244, h1245, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1238, h1244, h895, hlam]
                · linarith only [h1240, h1241, h1243, h895, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
              · linarith only [h1238, h1241, h1242, h895, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1282 | h1282
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1283 | h1283
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1284 | h1284
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1285 | h1285
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1286 | h1286
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1287 | h1287
                        · rcases h4bigk with h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [hlam, p1288_0]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [h0, hlam, p1288_1]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [h895, hlam, p1288_0]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [h1287, hc04, hlam, hphi, ht0b, ht45, ht5b, p1288_1, u4ehi4]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            rcases p1288_3 (m.d 0 4) (by simp) with h1293 | h1293
                            · rcases p1288_3 (m.d 1 4) (by simp) with h1294 | h1294
                              · rcases p1288_3 (m.d 2 4) (by simp) with h1295 | h1295
                                · rcases p1288_3 (m.d 3 4) (by simp) with h1296 | h1296
                                  · linarith only [h1238, h1296, hlam]
                                  · linarith only [h1287, h1296, hlam]
                                · linarith only [h1286, h1295, hlam]
                              · linarith only [h1283, h1294, hlam]
                            · linarith only [h1293, hlam, p1288_0]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [h1240, h1241, h1284, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1288_1, u4ehi4]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [hlam, p1288_0]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [h1241, hlam, p1288_0]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [h1241, h1284, h1287, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1288_1, u4ehi4]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            rcases p1288_3 (m.d 0 4) (by simp) with h1306 | h1306
                            · linarith only [h0, h1306, hlam]
                            · linarith only [h1240, h1306, hlam]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [h1238, h1284, h1287, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1288_1, u4ehi4]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [h0, h1284, hc01, hc23, hlam, hphi, ht12, p1288_1]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [hlam, p1288_0]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [h1284, h1287, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1288_1, u4ehi4]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            rcases p1288_3 (m.d 0 4) (by simp) with h1313 | h1313
                            · linarith only [h1313, h895, hlam]
                            · linarith only [h1240, h1313, hlam]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [h1238, hlam, p1288_1]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [h1282, hlam, p1288_1]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [h1284, hlam, p1288_0]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [hlam, p1288_0]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [h1282, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1288_1, u4ehi4]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [h1240, hlam, p1288_0]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [h1283, hlam, p1288_0]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [h1286, hlam, p1288_0]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [h1287, hlam, p1288_0]
                          · obtain ⟨p1288_0, p1288_1, p1288_2, p1288_3⟩ := h1288c
                            linarith only [hlam, p1288_0]
                        · rcases h4bigk with h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [hlam, p1326_0]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [h0, hlam, p1326_1]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [h895, hlam, p1326_0]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            rcases p1326_3 (m.d 0 4) (by simp) with h1330 | h1330
                            · rcases p1326_3 (m.d 1 4) (by simp) with h1331 | h1331
                              · rcases p1326_3 (m.d 2 4) (by simp) with h1332 | h1332
                                · rcases p1326_3 (m.d 3 4) (by simp) with h1333 | h1333
                                  · linarith only [h1238, h1333, hlam]
                                  · rcases p1326_3 (m.d 4 5) (by simp) with h1335 | h1335
                                    · linarith only [h1240, h1335, hlam]
                                    · linarith only [h1287, h1335, hlam]
                                · linarith only [h1284, h1332, hlam]
                              · linarith only [h1282, h1331, hlam]
                            · linarith only [h1238, h1330, hlam]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [h1287, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1326_1, u3ehi3]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [h1240, h1287, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1326_1, u3ehi3]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [hlam, p1326_0]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [h1241, hlam, p1326_0]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            rcases p1326_3 (m.d 0 4) (by simp) with h1345 | h1345
                            · linarith only [h0, h1345, hlam]
                            · linarith only [h1238, h1345, hlam]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [h1241, h1284, h1287, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1326_1, u3ehi3]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [h1240, h1284, h1287, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1326_1, u3ehi3]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [h0, h1284, hc01, hc23, hlam, hphi, ht12, p1326_1]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [hlam, p1326_0]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            rcases p1326_3 (m.d 0 4) (by simp) with h1352 | h1352
                            · linarith only [h1352, h895, hlam]
                            · linarith only [h1238, h1352, hlam]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [h1284, h1287, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1326_1, u3ehi3]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [h1238, hlam, p1326_1]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [h1282, hlam, p1326_1]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [h1284, hlam, p1326_0]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [hlam, p1326_0]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [h1287, hlam, p1326_0]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [h1240, hlam, p1326_0]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [h1283, hlam, p1326_0]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [h1286, hlam, p1326_0]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [h1240, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1326_1, u3ehi3]
                          · obtain ⟨p1326_0, p1326_1, p1326_2, p1326_3⟩ := h1326c
                            linarith only [hlam, p1326_0]
                      · linarith only [h0, h1240, h1241, h1286, hlam]
                    · linarith only [h0, h1239, h1240, h1241, h1284, h1285, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h1238, h1241, h1284, hlam]
                · linarith only [h0, h1240, h1283, hlam]
              · linarith only [h0, h1238, h1282, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1371 | h1371
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1372 | h1372
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1373 | h1373
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1374 | h1374
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1375 | h1375
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1376 | h1376
                      · linarith only [h1240, h1371, h1376, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1378 | h1378
                        · linarith only [h1238, h1376, h1378, h895, hlam]
                        · rcases h4bigk with h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [hlam, p1380_0]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [h0, hlam, p1380_1]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [h895, hlam, p1380_0]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [h1373, h1376, h895, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1380_1, u3ehi3]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [h1240, hlam, p1380_0]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            rcases p1380_3 (m.d 0 4) (by simp) with h1386 | h1386
                            · linarith only [h0, h1386, hlam]
                            · rcases p1380_3 (m.d 1 4) (by simp) with h1388 | h1388
                              · rcases p1380_3 (m.d 2 4) (by simp) with h1389 | h1389
                                · linarith only [h1371, h1389, hlam]
                                · linarith only [h1389, h895, hlam]
                              · linarith only [h0, h1388, hlam]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [hlam, p1380_0]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            rcases p1380_3 (m.d 0 4) (by simp) with h1394 | h1394
                            · linarith only [h0, h1394, hlam]
                            · rcases p1380_3 (m.d 1 4) (by simp) with h1396 | h1396
                              · rcases p1380_3 (m.d 2 4) (by simp) with h1397 | h1397
                                · linarith only [h1371, h1397, hlam]
                                · rcases p1380_3 (m.d 3 4) (by simp) with h1399 | h1399
                                  · linarith only [h1372, h1399, hlam]
                                  · rcases p1380_3 (m.d 4 5) (by simp) with h1401 | h1401
                                    · linarith only [h1373, h1401, hlam]
                                    · linarith only [h1376, h1401, hlam]
                              · linarith only [h1371, h1396, hlam]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            rcases p1380_3 (m.d 0 4) (by simp) with h1405 | h1405
                            · linarith only [h0, h1405, hlam]
                            · linarith only [h1238, h1405, hlam]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [h1371, h1376, h895, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1380_1]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [h1376, hc45, hlam, hphi, p1380_1, u4ehi0]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [h1371, hlam, p1380_1]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [hlam, p1380_0]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [h1371, h1373, h1376, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1380_1, u3ehi3]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [h1376, hlam, p1380_0]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [h1238, hlam, p1380_1]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [h1372, hlam, p1380_1]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [h1374, hlam, p1380_0]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [hlam, p1380_0]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [h1378, hlam, p1380_0]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [h1238, h1371, h1373, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1380_1, u3ehi3]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [h1373, hlam, p1380_0]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [h1371, h1373, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1380_1, u4ehi2]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [h1371, h1373, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1380_1, u3ehi3]
                          · obtain ⟨p1380_0, p1380_1, p1380_2, p1380_3⟩ := h1380c
                            linarith only [hlam, p1380_0]
                    · linarith only [h1374, h1375, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1238, h1240, h1371, h1373, h1374, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1426 | h1426
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1427 | h1427
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1428 | h1428
                      · linarith only [h1371, h1373, h1428, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1430 | h1430
                        · linarith only [h1238, h1371, h1373, h1430, h895, hlam]
                        · rcases h4bigk with h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [hlam, p1432_0]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h0, hlam, p1432_1]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h895, hlam, p1432_0]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h1371, h1373, h895, hc45, hlam, hphi, p1432_1, u4ehi3]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h1240, hlam, p1432_0]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h1373, hc45, hlam, hphi, p1432_1, u4ehi0]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [hlam, p1432_0]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h1373, hc45, hlam, hphi, p1432_1, u4ehi2]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h1373, hc45, hlam, hphi, ht34, p1432_1, u3ehi3]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h1373, hlam, p1432_0]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h1238, h1371, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1432_1, u3ehi3]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h1371, hlam, p1432_1]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [hlam, p1432_0]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h1371, h1373, hc45, hlam, hphi, ht34, p1432_1, u3ehi3]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h1428, hlam, p1432_0]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h1238, hlam, p1432_1]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h1372, hlam, p1432_1]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h1426, hlam, p1432_0]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [hlam, p1432_0]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h1430, hlam, p1432_0]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h1238, hc45, hlam, hphi, ht34, p1432_1, u3ehi3]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [hc45, hlam, hphi, p1432_1, u4ehi1]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [h895, hc02, hc45, hlam, hphi, ht23, ht34, p1432_1]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [hc45, hlam, hphi, ht34, p1432_1, u3ehi3]
                          · obtain ⟨p1432_0, p1432_1, p1432_2, p1432_3⟩ := h1432c
                            linarith only [hlam, p1432_0]
                    · linarith only [h1426, h1427, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1238, h1240, h1426, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h1238, h1240, h1372, hc45, hlam, hphi, ht34, u3ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1461 | h1461
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1462 | h1462
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1463 | h1463
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1464 | h1464
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1465 | h1465
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1466 | h1466
                        · linarith only [h1238, h1240, h1466, hlam]
                        · rcases h4bigk with h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [hlam, p1468_0]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [h0, hlam, p1468_1]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [h895, hlam, p1468_0]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [h1240, h1371, h1462, h1463, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1468_1, u4ehi3]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [h1240, hlam, p1468_0]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            rcases p1468_3 (m.d 0 4) (by simp) with h1474 | h1474
                            · linarith only [h0, h1474, hlam]
                            · rcases p1468_3 (m.d 1 4) (by simp) with h1476 | h1476
                              · rcases p1468_3 (m.d 2 4) (by simp) with h1477 | h1477
                                · rcases p1468_3 (m.d 3 4) (by simp) with h1478 | h1478
                                  · linarith only [h1461, h1478, hlam]
                                  · rcases p1468_3 (m.d 4 5) (by simp) with h1480 | h1480
                                    · linarith only [h1462, h1480, hlam]
                                    · linarith only [h1240, h1480, hlam]
                                · linarith only [h1477, h895, hlam]
                              · linarith only [h0, h1476, hlam]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [hlam, p1468_0]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [h1371, hlam, p1468_0]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            rcases p1468_3 (m.d 0 4) (by simp) with h1487 | h1487
                            · linarith only [h0, h1487, hlam]
                            · linarith only [h1238, h1487, hlam]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [h1240, h1371, h1463, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1468_1, u4ehi0]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            rcases p1468_3 (m.d 0 4) (by simp) with h1491 | h1491
                            · linarith only [h1491, h895, hlam]
                            · rcases p1468_3 (m.d 1 4) (by simp) with h1493 | h1493
                              · linarith only [h1371, h1493, hlam]
                              · linarith only [h0, h1493, hlam]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [h0, h1463, hc01, hc23, hlam, hphi, ht12, p1468_1]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [hlam, p1468_0]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            rcases p1468_3 (m.d 0 4) (by simp) with h1498 | h1498
                            · linarith only [h1498, h895, hlam]
                            · linarith only [h1238, h1498, hlam]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [h1238, h1240, h1463, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1468_1, u3ehi3]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [h1238, hlam, p1468_1]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [h1461, hlam, p1468_1]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [h1463, hlam, p1468_0]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [hlam, p1468_0]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [h1466, hlam, p1468_0]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [h1238, h1461, h1462, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1468_1, u3ehi3]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [h1462, hlam, p1468_0]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [h1465, hlam, p1468_0]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [h1371, h1462, h1463, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1468_1, u3ehi3]
                          · obtain ⟨p1468_0, p1468_1, p1468_2, p1468_3⟩ := h1468c
                            linarith only [hlam, p1468_0]
                      · linarith only [h1371, h1462, h1465, hlam]
                    · linarith only [h1239, h1240, h1371, h1462, h1463, h1464, hlam]
                  · linarith only [h1238, h1240, h1371, h1462, h1463, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1515 | h1515
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1516 | h1516
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1517 | h1517
                      · linarith only [h0, h1462, h1515, h1517, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1519 | h1519
                        · linarith only [h0, h1238, h1371, h1517, h1519, hlam]
                        · rcases h4bigk with h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [hlam, p1521_0]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h0, hlam, p1521_1]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h895, hlam, p1521_0]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h0, h1371, h1517, hc45, hlam, hphi, p1521_1, u4ehi3]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h1240, hlam, p1521_0]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h1371, h1517, hc45, hlam, hphi, p1521_1, u4ehi0]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [hlam, p1521_0]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h1371, hlam, p1521_0]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h1371, h1517, hc45, hlam, hphi, ht34, p1521_1, u3ehi3]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h1462, hlam, p1521_0]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h1238, h1517, hc45, hlam, hphi, ht34, p1521_1, u3ehi3]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h0, h1517, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1521_1]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [hlam, p1521_0]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h1517, hc45, hlam, hphi, ht34, p1521_1, u3ehi3]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h1517, hlam, p1521_0]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h1238, hlam, p1521_1]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h1461, hlam, p1521_1]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h1515, hlam, p1521_0]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [hlam, p1521_0]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h1519, hlam, p1521_0]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h1238, hc45, hlam, hphi, ht34, p1521_1, u3ehi3]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1521_1]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [h1371, hc12, hc45, hlam, hphi, ht23, ht34, p1521_1]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [hc45, hlam, hphi, ht34, p1521_1, u3ehi3]
                          · obtain ⟨p1521_0, p1521_1, p1521_2, p1521_3⟩ := h1521c
                            linarith only [hlam, p1521_0]
                    · linarith only [h1515, h1516, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1238, h1240, h1515, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h1238, h1240, h1461, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h1238, h1239, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1551 | h1551
        · linarith only [h1238, h1551, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1553 | h1553
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1554 | h1554
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1555 | h1555
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1556 | h1556
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1557 | h1557
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1558 | h1558
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1559 | h1559
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1560 | h1560
                        · rcases h4bigk with h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [hlam, p1561_0]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h0, hlam, p1561_1]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h895, hlam, p1561_0]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h1238, hlam, p1561_0]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h1554, h895, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1561_1, u4ehi4]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h1553, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1561_1, u4ehi4]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [hlam, p1561_0]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h1551, h1554, h1558, h1559, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1561_1, u3ehi0]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h1238, h1554, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1561_1, u3ehi0]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            rcases p1561_3 (m.d 0 4) (by simp) with h1571 | h1571
                            · linarith only [h0, h1571, hlam]
                            · linarith only [h1553, h1571, hlam]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h1553, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1561_1, u4ehi4]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h1554, hlam, p1561_1]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [hlam, p1561_0]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h1551, h1554, h1560, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1561_1, u3ehi0]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h1554, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1561_1, u4ehi4]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h1553, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1561_1, u4ehi4]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h1555, hlam, p1561_1]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h1557, hlam, p1561_0]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [hlam, p1561_0]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h1557, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1561_1, u4ehi4]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h1553, hlam, p1561_0]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h1556, hlam, p1561_0]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h1559, hlam, p1561_0]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [h1560, hlam, p1561_0]
                          · obtain ⟨p1561_0, p1561_1, p1561_2, p1561_3⟩ := h1561c
                            linarith only [hlam, p1561_0]
                        · linarith only [h1553, h1554, h1560, h895, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1238, h1553, h1559, h895, hc02, hc34, hlam, hphi, ht23]
                    · linarith only [h1238, h1553, h1557, h1558, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1592 | h1592
                    · linarith only [h1557, h1592, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1594 | h1594
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1595 | h1595
                        · rcases h4bigk with h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [hlam, p1596_0]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h0, hlam, p1596_1]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h895, hlam, p1596_0]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h1238, hlam, p1596_0]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h1238, h1555, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1596_1, u4ehi4]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h1553, h1554, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1596_1, u4ehi4]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [hlam, p1596_0]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h1553, h1554, h895, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1596_1, u4ehi4]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h1238, h1554, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1596_1, u3ehi0]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            rcases p1596_3 (m.d 0 4) (by simp) with h1606 | h1606
                            · linarith only [h0, h1606, hlam]
                            · linarith only [h1553, h1606, hlam]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h1553, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1596_1, u4ehi4]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h1554, hlam, p1596_1]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [hlam, p1596_0]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h1557, hlam, p1596_1]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h1555, h1557, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1596_1, u4ehi4]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h1553, h1555, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1596_1, u4ehi4]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h1555, hlam, p1596_1]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h1555, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1596_1, u4ehi2]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [hlam, p1596_0]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h1555, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1596_1, u4ehi4]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h1553, hlam, p1596_0]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h1556, hlam, p1596_0]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h1594, hlam, p1596_0]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [h1595, hlam, p1596_0]
                          · obtain ⟨p1596_0, p1596_1, p1596_2, p1596_3⟩ := h1596c
                            linarith only [hlam, p1596_0]
                        · linarith only [h1238, h1553, h1595, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h1553, h1594, h895, hlam]
                · linarith only [h0, h1553, h1556, h895, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1627 | h1627
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1628 | h1628
                  · linarith only [h1554, h1555, h1628, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1630 | h1630
                    · linarith only [h1551, h1628, h1630, hc34, hlam, hphi, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1632 | h1632
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1633 | h1633
                        · rcases h4bigk with h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [hlam, p1634_0]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h0, hlam, p1634_1]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h895, hlam, p1634_0]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h1238, hlam, p1634_0]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h1554, h895, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1634_1, u4ehi4]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h1553, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1634_1, u4ehi4]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [hlam, p1634_0]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h1553, h1554, h895, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1634_1, u4ehi4]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h1555, hlam, p1634_0]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            rcases p1634_3 (m.d 0 4) (by simp) with h1644 | h1644
                            · linarith only [h0, h1644, hlam]
                            · linarith only [h1553, h1644, hlam]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h1553, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1634_1, u4ehi4]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h1554, hlam, p1634_1]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [hlam, p1634_0]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h1628, hlam, p1634_1]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h1554, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1634_1, u4ehi4]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h1553, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1634_1, u4ehi4]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1634_1]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h1553, h895, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1634_1, u4ehi4]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [hlam, p1634_0]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            rcases p1634_3 (m.d 0 4) (by simp) with h1656 | h1656
                            · linarith only [h1238, h1656, hlam]
                            · linarith only [h1553, h1656, hlam]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h1553, hlam, p1634_0]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h1627, hlam, p1634_0]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h1632, hlam, p1634_0]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [h1633, hlam, p1634_0]
                          · obtain ⟨p1634_0, p1634_1, p1634_2, p1634_3⟩ := h1634c
                            linarith only [hlam, p1634_0]
                        · linarith only [h1238, h1553, h1633, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h1553, h1632, h895, hlam]
                · linarith only [h1553, h1554, h1627, h895, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1667 | h1667
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1668 | h1668
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1669 | h1669
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1670 | h1670
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1671 | h1671
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1672 | h1672
                        · rcases h4bigk with h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [hlam, p1673_0]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h0, hlam, p1673_1]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h895, hlam, p1673_0]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h1238, hlam, p1673_0]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h1238, h1669, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1673_1, u4ehi4]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h1553, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1673_1, u4ehi4]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [hlam, p1673_0]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h1554, hlam, p1673_0]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h1238, h1554, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1673_1, u3ehi0]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            rcases p1673_3 (m.d 0 4) (by simp) with h1683 | h1683
                            · linarith only [h0, h1683, hlam]
                            · linarith only [h1553, h1683, hlam]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h1553, h1669, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1673_1, u4ehi4]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h0, h1669, hc01, hc23, hlam, hphi, ht12, p1673_1]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [hlam, p1673_0]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h1551, h1669, h1672, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1673_1, u3ehi0]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            rcases p1673_3 (m.d 0 4) (by simp) with h1690 | h1690
                            · linarith only [h1690, h895, hlam]
                            · linarith only [h1553, h1690, hlam]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h1553, h1667, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1673_1, u4ehi4]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h1667, hlam, p1673_1]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h1669, hlam, p1673_0]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [hlam, p1673_0]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h1669, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1673_1, u4ehi4]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h1553, hlam, p1673_0]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h1668, hlam, p1673_0]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h1671, hlam, p1673_0]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [h1672, hlam, p1673_0]
                          · obtain ⟨p1673_0, p1673_1, p1673_2, p1673_3⟩ := h1673c
                            linarith only [hlam, p1673_0]
                        · linarith only [h1238, h1553, h1672, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h1238, h1553, h1554, h1667, h1671, hlam]
                    · linarith only [h1238, h1553, h1669, h1670, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · linarith only [h1554, h1667, h1669, hlam]
                · linarith only [h1238, h1553, h1667, h1668, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1708 | h1708
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1709 | h1709
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1710 | h1710
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1711 | h1711
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1712 | h1712
                        · rcases h4bigk with h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c | h1713c
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [hlam, p1713_0]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h0, hlam, p1713_1]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h895, hlam, p1713_0]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h1238, hlam, p1713_0]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h0, h1667, h1709, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1713_1, u4ehi4]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h1238, h1667, hc34, hlam, hphi, p1713_1, u3ehi0]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [hlam, p1713_0]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h1554, hlam, p1713_0]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h1667, hlam, p1713_0]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h1667, h1709, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1713_1, u4ehi4]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h1553, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1713_1, u4ehi4]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p1713_1]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [hlam, p1713_0]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h1667, h1709, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1713_1, u3ehi1]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            rcases p1713_3 (m.d 0 4) (by simp) with h1728 | h1728
                            · linarith only [h1728, h895, hlam]
                            · linarith only [h1553, h1728, hlam]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h1553, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1713_1, u4ehi4]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h0, h1553, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1713_1, u4ehi4]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h1709, hlam, p1713_0]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [hlam, p1713_0]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h1709, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1713_1, u4ehi4]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h1553, hlam, p1713_0]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h1708, hlam, p1713_0]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h1711, hlam, p1713_0]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [h1712, hlam, p1713_0]
                          · obtain ⟨p1713_0, p1713_1, p1713_2, p1713_3⟩ := h1713c
                            linarith only [hlam, p1713_0]
                        · linarith only [h1238, h1553, h1712, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h0, h1553, h1667, h1709, h1711, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1553, h1667, h1709, h1710, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1744 | h1744
                    · linarith only [h1709, h1744, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1746 | h1746
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1747 | h1747
                        · rcases h4bigk with h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [hlam, p1748_0]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [h0, hlam, p1748_1]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [h895, hlam, p1748_0]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [h1238, hlam, p1748_0]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            rcases p1748_3 (m.d 0 4) (by simp) with h1753 | h1753
                            · rcases p1748_3 (m.d 1 4) (by simp) with h1754 | h1754
                              · rcases p1748_3 (m.d 2 4) (by simp) with h1755 | h1755
                                · rcases p1748_3 (m.d 3 4) (by simp) with h1756 | h1756
                                  · rcases p1748_3 (m.d 4 5) (by simp) with h1757 | h1757
                                    · linarith only [h1757, hlam, p1748_0]
                                    · rcases h5emax with h1759 | h1759 | h1759 | h1759 | h1759
                                      · linarith only [h1551, h1759, hlam, ht34, ht45, u3ehi0]
                                      · linarith only [h1708, h1759, hlam, ht45, u4ehi4]
                                      · linarith only [h0, h1554, h1709, h1744, h1759, hc34, hlam, hphi, ht45, p1748_1, u3ehi2, u4ehi4]
                                      · linarith only [h0, h1551, h1554, h1709, h1759, hc34, hlam, hphi, ht45, p1748_1, u3ehi0, u4ehi4]
                                      · linarith only [h1759, hlam, ht45, u4ehi4]
                                  · linarith only [h1747, h1756, hlam]
                                · linarith only [h1746, h1755, hlam]
                              · linarith only [h1708, h1754, hlam]
                            · linarith only [h1753, hlam, p1748_0]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [h1238, h1554, h1709, hc34, hlam, hphi, p1748_1, u3ehi0]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [hlam, p1748_0]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [h1554, hlam, p1748_0]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [h1667, hlam, p1748_0]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            rcases p1748_3 (m.d 0 4) (by simp) with h1773 | h1773
                            · linarith only [h0, h1773, hlam]
                            · linarith only [h1553, h1773, hlam]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [h1553, h1709, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1748_1, u4ehi4]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [h0, h1709, hc01, hc34, hlam, hphi, ht12, ht23, p1748_1]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [hlam, p1748_0]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [h1709, hlam, p1748_1]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            rcases p1748_3 (m.d 0 4) (by simp) with h1780 | h1780
                            · linarith only [h1780, h895, hlam]
                            · linarith only [h1553, h1780, hlam]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [h1553, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1748_1, u4ehi4]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [h0, h1553, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1748_1, u4ehi4]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [h895, hc02, hc34, hlam, hphi, ht23, p1748_1]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [hlam, p1748_0]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            rcases p1748_3 (m.d 0 4) (by simp) with h1787 | h1787
                            · linarith only [h1238, h1787, hlam]
                            · linarith only [h1553, h1787, hlam]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [h1553, hlam, p1748_0]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [h1708, hlam, p1748_0]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [h1746, hlam, p1748_0]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [h1747, hlam, p1748_0]
                          · obtain ⟨p1748_0, p1748_1, p1748_2, p1748_3⟩ := h1748c
                            linarith only [hlam, p1748_0]
                        · linarith only [h1238, h1553, h1747, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h0, h1553, h1554, h1746, hlam]
                · linarith only [h0, h1553, h1708, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1798 | h1798
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1799 | h1799
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1800 | h1800
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1801 | h1801
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1802 | h1802
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1803 | h1803
                      · linarith only [h1553, h1798, h1803, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                      · linarith only [h1238, h1798, h1800, h1801, h1803, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h1238, h1801, h1802, hc35, hlam, hphi, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1807 | h1807
                    · linarith only [h1801, h1807, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1809 | h1809
                      · linarith only [h1238, h1553, h1799, h1801, h1809, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1811 | h1811
                        · linarith only [h1799, h1809, h1811, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h1238, h1811, hc45, hlam, hphi, ht34, u3ehi0]
                · linarith only [h1238, h1799, h1800, hc45, hlam, hphi, ht34, u3ehi0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1815 | h1815
                · linarith only [h1238, h1553, h1799, h1815, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1817 | h1817
                  · linarith only [h1798, h1799, h1815, h1817, hc45, hlam, hphi, ht34, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1819 | h1819
                    · linarith only [h1551, h1817, h1819, hc34, hlam, hphi, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1821 | h1821
                      · linarith only [h1798, h1815, h1821, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1823 | h1823
                        · linarith only [h0, h1815, h1823, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1238, h1823, hc45, hlam, hphi, ht34, u3ehi0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1826 | h1826
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1827 | h1827
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1828 | h1828
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1829 | h1829
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1830 | h1830
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1831 | h1831
                        · linarith only [h1238, h1553, h1831, hc34, hlam, hphi, u3ehi0]
                        · linarith only [h1238, h1798, h1827, h1828, h1831, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h1798, h1827, h1830, hlam]
                    · linarith only [h1238, h1553, h1798, h1827, h1828, h1829, hc35, hlam, hphi, u3ehi0]
                  · linarith only [h1238, h1553, h1798, h1827, h1828, hc34, hlam, hphi, u3ehi0]
                · linarith only [h1238, h1826, h1827, hc45, hlam, hphi, ht34, u3ehi0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1838 | h1838
                · linarith only [h1238, h1553, h1826, h1838, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1840 | h1840
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1841 | h1841
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1842 | h1842
                      · linarith only [h0, h1838, h1842, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h1826, h1840, h1842, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h1826, h1840, h1841, hc35, hlam, hphi, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1846 | h1846
                    · linarith only [h1840, h1846, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1848 | h1848
                      · linarith only [h0, h1838, h1840, h1848, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1850 | h1850
                        · linarith only [h0, h1798, h1848, h1850, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1238, h1850, hc45, hlam, hphi, ht34, u3ehi0]

set_option maxHeartbeats 3648000 in
theorem n7l_sAB3_M_IR_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.2.1
  have h3ehi := hb3.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
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
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h11, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                        · linarith only [h0, h14, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h0, h14, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h17 | h17
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                        · linarith only [h18, h7, h9, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                          · linarith only [h0, h20, h3, h5, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                            · linarith only [h0, h22, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h17, h2, h22, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                        · linarith only [h25, h7, h9, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                          · linarith only [h0, h17, h27, h3, h5, h6, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
                            · linarith only [h0, h17, h29, h4, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h31 | h31
                              · linarith only [h17, h31, h7, h9, hc34, hlam, hphi, u3ehi2]
                              · linarith only [h31, h6, h7, h9, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h4, h7, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
                  · linarith only [h0, h3, h35, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h37 | h37
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h38 | h38
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h40 | h40
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h41 | h41
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h42 | h42
                              · linarith only [h0, h3, h37, h42, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h2, h38, h42, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h35, h38, h41, hlam]
                          · linarith only [h37, h40, h7, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h37, h39, h7, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h48 | h48
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h49 | h49
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h50 | h50
                            · linarith only [h0, h37, h38, h4, h50, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h52 | h52
                              · linarith only [h35, h37, h50, h52, hlam]
                              · rcases h4bigk with h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [hlam, p54_0]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  rcases p54_3 (m.d 0 4) (by simp) with h56 | h56
                                  · rcases p54_3 (m.d 1 4) (by simp) with h57 | h57
                                    · linarith only [h2, h57, hlam]
                                    · rcases p54_3 (m.d 2 4) (by simp) with h59 | h59
                                      · linarith only [h4, h59, hlam]
                                      · linarith only [h35, h59, hlam]
                                  · linarith only [h2, h56, hlam]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  rcases p54_3 (m.d 0 4) (by simp) with h63 | h63
                                  · rcases p54_3 (m.d 1 4) (by simp) with h64 | h64
                                    · linarith only [h2, h64, hlam]
                                    · rcases p54_3 (m.d 2 4) (by simp) with h66 | h66
                                      · linarith only [h4, h66, hlam]
                                      · rcases p54_3 (m.d 3 4) (by simp) with h68 | h68
                                        · linarith only [h5, h68, hlam]
                                        · rcases p54_3 (m.d 4 5) (by simp) with h70 | h70
                                          · linarith only [h6, h70, hlam]
                                          · linarith only [h50, h70, hlam]
                                  · linarith only [h4, h63, hlam]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  rcases p54_3 (m.d 0 4) (by simp) with h74 | h74
                                  · rcases p54_3 (m.d 1 4) (by simp) with h75 | h75
                                    · linarith only [h2, h75, hlam]
                                    · linarith only [h37, h75, hlam]
                                  · linarith only [h5, h74, hlam]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [h35, h37, h5, h50, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1, u3ehi3]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [h2, hlam, p54_0]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [hlam, p54_0]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [h35, hlam, p54_0]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [h35, h50, hc45, hlam, hphi, ht34, p54_1, u3ehi3]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [h38, hlam, p54_0]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [h4, hlam, p54_1]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [h50, hc45, hlam, hphi, p54_1, u4ehi1]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [hlam, p54_0]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [h0, h3, h5, h50, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1, u3ehi3]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [h50, hlam, p54_0]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [h5, hlam, p54_1]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [h37, hlam, p54_1]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [h48, hlam, p54_0]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [hlam, p54_0]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [h52, hlam, p54_0]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [h6, hlam, p54_0]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [h0, h3, h37, h5, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1, u3ehi3]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [h0, h3, h35, h5, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p54_1]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [h0, h3, h5, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1, u3ehi3]
                                · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                  linarith only [hlam, p54_0]
                          · linarith only [h37, h49, h7, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h37, h48, h7, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h102 | h102
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h103 | h103
                        · linarith only [h0, h103, h3, h37, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h105 | h105
                          · linarith only [h103, h105, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h107 | h107
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h108 | h108
                              · rcases h4bigk with h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [hlam, p109_0]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h0, h102, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p109_1, u4ehi4]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h0, h102, h3, h35, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p109_1, u4ehi4]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h0, h105, h108, h3, h5, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p109_1, u3ehi1]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  rcases p109_3 (m.d 0 4) (by simp) with h114 | h114
                                  · rcases p109_3 (m.d 1 4) (by simp) with h115 | h115
                                    · linarith only [h115, h2, hlam]
                                    · linarith only [h102, h115, hlam]
                                  · linarith only [h114, hlam, p109_0]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h2, hlam, p109_0]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [hlam, p109_0]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h35, hlam, p109_0]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h37, hlam, p109_0]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p109_1, u4ehi4]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h4, hlam, p109_1]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p109_1, u4ehi1]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [hlam, p109_0]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h103, hlam, p109_1]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p109_1, u4ehi4]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h5, hlam, p109_1]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h0, h102, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p109_1, u4ehi4]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p109_1, u4ehi2]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [hlam, p109_0]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p109_1, u4ehi4]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h6, hlam, p109_0]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h102, hlam, p109_0]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h107, hlam, p109_0]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [h108, hlam, p109_0]
                                · obtain ⟨p109_0, p109_1, p109_2, p109_3⟩ := h109c
                                  linarith only [hlam, p109_0]
                              · linarith only [h102, h108, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h102, h107, h35, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                        · linarith only [h0, h141, h3, h37, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h143 | h143
                          · linarith only [h141, h143, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h145 | h145
                            · linarith only [h0, h102, h141, h145, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h147 | h147
                              · linarith only [h0, h145, h147, h3, h35, h37, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · linarith only [h147, h37, hc45, hlam, hphi, ht34, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h150 | h150
                · rcases m.htr 1 2 4 (by decide) (by decide) with h151 | h151
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h153 | h153
                      · linarith only [h153, h2, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                        · linarith only [h0, h150, h155, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h152, h155, h2, h6, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h152, h5, h6, hc45, hlam, hphi, ht34, u3ehi1]
                  · linarith only [h150, h151, h4, h6, hc45, hlam, hphi, ht34, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h160 | h160
                  · linarith only [h0, h150, h160, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h162 | h162
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h163 | h163
                      · linarith only [h160, h163, h4, h6, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h166 | h166
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h167 | h167
                            · linarith only [h167, h4, h6, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h169 | h169
                              · linarith only [h162, h169, h6, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                              · rcases h4bigk with h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [hlam, p171_0]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h162, h6, hc45, hlam, hphi, ht34, p171_1, u3ehi3]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h160, h162, h6, hc45, hlam, hphi, ht34, p171_1, u3ehi3]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h6, hc45, hlam, hphi, ht34, p171_1, u3ehi3]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h6, hlam, p171_0]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h2, hlam, p171_0]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [hlam, p171_0]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h160, hlam, p171_0]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p171_1, u3ehi3]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h163, hlam, p171_0]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h4, hlam, p171_1]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p171_1, u4ehi1]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [hlam, p171_0]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h4, h6, hc45, hlam, hphi, ht34, p171_1, u3ehi3]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h167, hlam, p171_0]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h5, hlam, p171_1]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h162, hlam, p171_1]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h165, hlam, p171_0]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [hlam, p171_0]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h169, hlam, p171_0]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [hc45, hlam, hphi, p171_1, u4ehi0]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h162, hc45, hlam, hphi, ht34, p171_1, u3ehi3]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [h160, hc12, hc45, hlam, hphi, ht23, ht34, p171_1]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [hc45, hlam, hphi, ht34, p171_1, u3ehi3]
                                · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                  linarith only [hlam, p171_0]
                          · linarith only [h150, h162, h166, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h150, h162, h165, hlam]
                    · linarith only [h162, h5, h6, hc45, hlam, hphi, ht34, u3ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h200 | h200
              · rcases m.htr 1 2 3 (by decide) (by decide) with h201 | h201
                · rcases m.htr 1 2 4 (by decide) (by decide) with h202 | h202
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h203 | h203
                    · linarith only [h1, h203, h5, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h205 | h205
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h206 | h206
                        · linarith only [h201, h206, h5, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h208 | h208
                          · linarith only [h1, h201, h208, h5, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h210 | h210
                            · linarith only [h0, h202, h210, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h2, h205, h206, h210, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h200, h203, h205, h5, hc34, hlam, hphi, u3ehi1]
                  · linarith only [h0, h201, h202, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h215 | h215
                  · linarith only [h0, h201, h215, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h217 | h217
                    · linarith only [h201, h217, h3, h5, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h219 | h219
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h220 | h220
                        · linarith only [h220, h3, h5, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h222 | h222
                          · linarith only [h222, h3, h5, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h224 | h224
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h225 | h225
                              · rcases h4bigk with h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [hlam, p226_0]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h219, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p226_1, u4ehi4]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h215, h219, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p226_1, u4ehi4]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h5, hlam, p226_0]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  rcases p226_3 (m.d 0 4) (by simp) with h231 | h231
                                  · rcases p226_3 (m.d 1 4) (by simp) with h232 | h232
                                    · linarith only [h2, h232, hlam]
                                    · linarith only [h219, h232, hlam]
                                  · linarith only [h231, hlam, p226_0]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h2, hlam, p226_0]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [hlam, p226_0]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h215, hlam, p226_0]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h217, hlam, p226_0]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p226_1, u4ehi4]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h4, hlam, p226_1]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p226_1, u4ehi1]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [hlam, p226_0]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h220, hlam, p226_1]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p226_1, u4ehi4]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h2, h219, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p226_1, u4ehi4]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h219, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p226_1, u4ehi4]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h215, hc12, hc34, hlam, hphi, ht23, p226_1]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [hlam, p226_0]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  rcases p226_3 (m.d 0 4) (by simp) with h250 | h250
                                  · linarith only [h250, h5, hlam]
                                  · linarith only [h200, h250, hlam]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h200, hlam, p226_0]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h219, hlam, p226_0]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h224, hlam, p226_0]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [h225, hlam, p226_0]
                                · obtain ⟨p226_0, p226_1, p226_2, p226_3⟩ := h226c
                                  linarith only [hlam, p226_0]
                              · linarith only [h219, h225, h5, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h215, h219, h224, hlam]
                      · linarith only [h200, h217, h219, h5, hc34, hlam, hphi, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h261 | h261
                · rcases m.htr 1 2 4 (by decide) (by decide) with h262 | h262
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h263 | h263
                    · linarith only [h1, h263, h5, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h265 | h265
                      · linarith only [h2, h200, h265, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h267 | h267
                        · linarith only [h1, h261, h267, h5, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h269 | h269
                          · linarith only [h1, h261, h269, h5, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h271 | h271
                            · linarith only [h200, h262, h271, h5, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h273 | h273
                              · linarith only [h1, h200, h261, h273, h5, hc34, hlam, hphi, u3ehi2]
                              · linarith only [h1, h261, h273, h5, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h0, h261, h262, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h277 | h277
                  · linarith only [h261, h277, h3, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h279 | h279
                    · linarith only [h1, h261, h279, h3, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h281 | h281
                      · linarith only [h200, h277, h281, h4, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h283 | h283
                        · linarith only [h283, h3, h5, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h285 | h285
                          · linarith only [h285, h3, h5, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h287 | h287
                            · linarith only [h200, h287, h4, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h289 | h289
                              · linarith only [h200, h289, h5, hc34, hlam, hphi, u3ehi0]
                              · linarith only [h261, h289, h3, h5, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h292 | h292
            · linarith only [h292, h3, h4, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h294 | h294
              · rcases m.htr 1 2 3 (by decide) (by decide) with h295 | h295
                · rcases m.htr 1 2 4 (by decide) (by decide) with h296 | h296
                  · linarith only [h0, h296, h4, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h298 | h298
                    · linarith only [h1, h292, h298, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h300 | h300
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h301 | h301
                        · linarith only [h1, h2, h292, h295, h300, h301, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h0, h295, h301, h4, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h295, h296, h300, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h295, h3, h4, hc12, hc24, hlam, hphi]
              · linarith only [h294, h3, h4, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h307 | h307
          · rcases m.htr 0 3 4 (by decide) (by decide) with h308 | h308
            · rcases m.htr 0 4 5 (by decide) (by decide) with h309 | h309
              · rcases m.htr 1 2 3 (by decide) (by decide) with h310 | h310
                · linarith only [h3, h307, h309, h310, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h312 | h312
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h313 | h313
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h314 | h314
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h315 | h315
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h316 | h316
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h317 | h317
                            · linarith only [h0, h3, h312, h317, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · linarith only [h2, h314, h315, h317, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h3, h312, h315, h316, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h0, h3, h312, h315, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                      · linarith only [h3, h307, h309, h314, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h3, h307, h308, h310, h312, h313, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · linarith only [h3, h307, h312, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h325 | h325
                · linarith only [h3, h307, h325, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h327 | h327
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h328 | h328
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h329 | h329
                      · linarith only [h2, h309, h329, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h331 | h331
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h332 | h332
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h333 | h333
                            · linarith only [h2, h309, h327, h333, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h335 | h335
                              · linarith only [h2, h309, h327, h331, h335, hlam]
                              · rcases h4bigk with h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [hlam, p337_0]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h309, h327, h331, hc45, hlam, hphi, ht34, p337_1, u3ehi3]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h309, h331, hc45, hlam, hphi, ht34, p337_1, u3ehi3]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h309, hc45, hlam, hphi, ht34, p337_1, u3ehi3]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h309, hlam, p337_0]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h2, hlam, p337_0]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [hlam, p337_0]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h2, h331, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p337_1, u3ehi3]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h2, h309, hc45, hlam, hphi, ht34, p337_1, u3ehi3]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h329, hlam, p337_0]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h307, hlam, p337_1]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h327, hlam, p337_1]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [hlam, p337_0]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h0, h327, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p337_1, u3ehi3]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h333, hlam, p337_0]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h308, hlam, p337_1]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h328, hlam, p337_1]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h331, hlam, p337_0]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [hlam, p337_0]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h335, hlam, p337_0]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [hc45, hlam, hphi, p337_1, u4ehi0]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h328, hc45, hlam, hphi, ht34, p337_1, u3ehi3]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [h331, hc45, hlam, hphi, ht34, p337_1, u3ehi3]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [hc45, hlam, hphi, ht34, p337_1, u3ehi3]
                                · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                  linarith only [hlam, p337_0]
                          · linarith only [h3, h307, h331, h332, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h0, h3, h327, h331, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · linarith only [h308, h309, h328, hc45, hlam, hphi, ht34, u3ehi1]
                  · linarith only [h3, h307, h327, hc12, hc23, hlam, hphi]
            · linarith only [h3, h307, h308, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h368 | h368
            · rcases m.htr 0 4 5 (by decide) (by decide) with h369 | h369
              · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
                · linarith only [h0, h3, h370, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h372 | h372
                  · linarith only [h0, h307, h372, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h374 | h374
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h375 | h375
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h376 | h376
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h377 | h377
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h378 | h378
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h379 | h379
                              · linarith only [h1, h374, h379, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h2, h375, h379, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h2, h3, h307, h368, h375, h378, hc12, hc23, hlam, hphi]
                          · linarith only [h3, h368, h377, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1, h3, h374, h376, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h385 | h385
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h386 | h386
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h387 | h387
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h388 | h388
                              · linarith only [h374, h375, h388, hlam]
                              · rcases h4bigk with h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [hlam, p390_0]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  rcases p390_3 (m.d 0 4) (by simp) with h392 | h392
                                  · rcases p390_3 (m.d 1 4) (by simp) with h393 | h393
                                    · linarith only [h2, h393, hlam]
                                    · rcases p390_3 (m.d 2 4) (by simp) with h395 | h395
                                      · rcases p390_3 (m.d 3 4) (by simp) with h396 | h396
                                        · linarith only [h368, h396, hlam]
                                        · rcases p390_3 (m.d 4 5) (by simp) with h398 | h398
                                          · linarith only [h369, h398, hlam]
                                          · linarith only [h375, h398, hlam]
                                      · linarith only [h372, h395, hlam]
                                  · linarith only [h2, h392, hlam]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [h307, hlam, p390_0]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  rcases p390_3 (m.d 0 4) (by simp) with h404 | h404
                                  · rcases p390_3 (m.d 1 4) (by simp) with h405 | h405
                                    · linarith only [h2, h405, hlam]
                                    · linarith only [h374, h405, hlam]
                                  · linarith only [h368, h404, hlam]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [h3, h368, h374, h375, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p390_1, u3ehi3]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [h2, hlam, p390_0]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [hlam, p390_0]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [h372, hlam, p390_0]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [h375, hc45, hlam, hphi, ht34, p390_1, u3ehi3]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [h375, hlam, p390_0]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [h369, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p390_1, u5ehi4]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  rcases p390_3 (m.d 0 4) (by simp) with h416 | h416
                                  · linarith only [h307, h416, hlam]
                                  · linarith only [h2, h416, hlam]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [hlam, p390_0]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  rcases p390_3 (m.d 0 4) (by simp) with h420 | h420
                                  · linarith only [h307, h420, hlam]
                                  · linarith only [h368, h420, hlam]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [h374, h375, h385, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p390_1, u3ehi3]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [h368, hlam, p390_1]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [h374, hlam, p390_1]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [h385, hlam, p390_0]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [hlam, p390_0]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [h388, hlam, p390_0]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [h369, hlam, p390_0]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [h369, h374, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p390_1, u3ehi3]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [h387, hlam, p390_0]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [h307, h369, h385, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p390_1, u3ehi3]
                                · obtain ⟨p390_0, p390_1, p390_2, p390_3⟩ := h390c
                                  linarith only [hlam, p390_0]
                            · linarith only [h307, h369, h387, hlam]
                          · linarith only [h3, h368, h386, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h3, h368, h369, h374, h375, h385, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h437 | h437
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h438 | h438
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h439 | h439
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h440 | h440
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h441 | h441
                              · rcases h4bigk with h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [hlam, p442_0]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h3, h368, h437, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p442_1, u4ehi4]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h307, hlam, p442_0]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h3, h368, h374, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p442_1, u3ehi1]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  rcases p442_3 (m.d 0 4) (by simp) with h447 | h447
                                  · rcases p442_3 (m.d 1 4) (by simp) with h448 | h448
                                    · linarith only [h2, h448, hlam]
                                    · linarith only [h437, h448, hlam]
                                  · linarith only [h447, hlam, p442_0]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h2, hlam, p442_0]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [hlam, p442_0]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h372, hlam, p442_0]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h374, hlam, p442_0]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p442_1, u4ehi4]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h368, h374, h438, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p442_1, u3ehi1]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h437, h438, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p442_1, u4ehi4]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [hlam, p442_0]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h374, h438, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p442_1, u3ehi1]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  rcases p442_3 (m.d 0 4) (by simp) with h461 | h461
                                  · linarith only [h307, h461, hlam]
                                  · linarith only [h369, h461, hlam]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h368, hlam, p442_1]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h368, h437, hc04, hlam, hphi, ht0b, ht45, ht5b, p442_1, u4ehi4]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h438, hlam, p442_0]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [hlam, p442_0]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h3, h368, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p442_1, u4ehi4]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h369, hlam, p442_0]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h437, hlam, p442_0]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h440, hlam, p442_0]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [h441, hlam, p442_0]
                                · obtain ⟨p442_0, p442_1, p442_2, p442_3⟩ := h442c
                                  linarith only [hlam, p442_0]
                              · linarith only [h374, h437, h441, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · linarith only [h3, h307, h368, h374, h437, h440, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                          · linarith only [h3, h368, h374, h439, hc35, hlam, hphi, u3ehi1]
                        · linarith only [h3, h368, h438, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h478 | h478
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h479 | h479
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h480 | h480
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h481 | h481
                              · linarith only [h3, h368, h374, h437, h481, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                              · linarith only [h369, h374, h481, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · linarith only [h0, h3, h307, h368, h369, h480, hc12, hc23, hlam, hphi]
                          · linarith only [h3, h368, h374, h479, hc35, hlam, hphi, u3ehi1]
                        · linarith only [h3, h368, h369, h374, h437, h478, hc34, hlam, hphi, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h487 | h487
                · linarith only [h0, h3, h487, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h489 | h489
                  · linarith only [h0, h307, h489, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h491 | h491
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h492 | h492
                      · linarith only [h2, h369, h492, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h494 | h494
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h495 | h495
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h496 | h496
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h497 | h497
                              · linarith only [h1, h369, h491, h497, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                              · rcases h4bigk with h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [hlam, p499_0]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [h369, h491, h494, h496, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p499_1, u3ehi3]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [h307, hlam, p499_0]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [h369, h494, h496, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p499_1, u3ehi3]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [h369, hlam, p499_0]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [h2, hlam, p499_0]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [hlam, p499_0]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [h489, hlam, p499_0]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p499_1, u3ehi3]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [h492, hlam, p499_0]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  rcases p499_3 (m.d 0 4) (by simp) with h510 | h510
                                  · linarith only [h307, h510, hlam]
                                  · rcases p499_3 (m.d 1 4) (by simp) with h512 | h512
                                    · linarith only [h489, h512, hlam]
                                    · rcases p499_3 (m.d 2 4) (by simp) with h514 | h514
                                      · rcases p499_3 (m.d 3 4) (by simp) with h515 | h515
                                        · linarith only [h494, h515, hlam]
                                        · rcases p499_3 (m.d 4 5) (by simp) with h517 | h517
                                          · linarith only [h496, h517, hlam]
                                          · linarith only [h369, h517, hlam]
                                      · linarith only [h307, h514, hlam]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  rcases p499_3 (m.d 0 4) (by simp) with h521 | h521
                                  · linarith only [h307, h521, hlam]
                                  · linarith only [h2, h521, hlam]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [hlam, p499_0]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  rcases p499_3 (m.d 0 4) (by simp) with h525 | h525
                                  · linarith only [h307, h525, hlam]
                                  · linarith only [h368, h525, hlam]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [h307, h369, h494, hc02, hc23, hlam, hphi, p499_1]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [h368, hlam, p499_1]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [h491, hlam, p499_1]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [h494, hlam, p499_0]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [hlam, p499_0]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [h497, hlam, p499_0]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [h2, hc45, hlam, hphi, p499_1, u4ehi1]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [h491, hc45, hlam, hphi, ht34, p499_1, u3ehi3]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [h496, hlam, p499_0]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [h494, h496, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p499_1, u3ehi3]
                                · obtain ⟨p499_0, p499_1, p499_2, p499_3⟩ := h499c
                                  linarith only [hlam, p499_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h539 | h539
                              · linarith only [h0, h307, h496, h539, hc12, hc34, hlam, hphi, ht23]
                              · rcases h4bigk with h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c | h541c
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [hlam, p541_0]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h307, h491, h496, hc45, hlam, hphi, ht34, p541_1, u3ehi3]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h307, hlam, p541_0]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h307, h496, hc45, hlam, hphi, ht34, p541_1, u3ehi3]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h369, hlam, p541_0]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h2, hlam, p541_0]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [hlam, p541_0]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h489, hlam, p541_0]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p541_1, u3ehi3]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h492, hlam, p541_0]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h496, hc45, hlam, hphi, p541_1, u4ehi0]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h496, hc45, hlam, hphi, p541_1, u4ehi1]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [hlam, p541_0]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h496, hc45, hlam, hphi, ht34, p541_1, u3ehi3]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h496, hlam, p541_0]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h368, hlam, p541_1]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h491, hlam, p541_1]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h494, hlam, p541_0]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [hlam, p541_0]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h539, hlam, p541_0]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [hc45, hlam, hphi, p541_1, u4ehi0]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h491, hc45, hlam, hphi, ht34, p541_1, u3ehi3]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [h307, hc02, hc45, hlam, hphi, ht23, ht34, p541_1]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [hc45, hlam, hphi, ht34, p541_1, u3ehi3]
                                · obtain ⟨p541_0, p541_1, p541_2, p541_3⟩ := h541c
                                  linarith only [hlam, p541_0]
                          · linarith only [h3, h368, h495, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1, h3, h491, h494, hlam]
                    · linarith only [h368, h369, h491, hc45, hlam, hphi, ht34, u3ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h570 | h570
              · rcases m.htr 1 2 3 (by decide) (by decide) with h571 | h571
                · linarith only [h0, h3, h571, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h573 | h573
                  · linarith only [h0, h307, h573, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h575 | h575
                    · linarith only [h1, h368, h575, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h577 | h577
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h578 | h578
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h579 | h579
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h580 | h580
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h581 | h581
                              · rcases h4bigk with h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [hlam, p582_0]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h577, hc04, hlam, hphi, ht0b, ht45, ht5b, p582_1, u4ehi4]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h307, hlam, p582_0]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h368, hlam, p582_0]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h368, h578, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p582_1, u4ehi4]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h2, hlam, p582_0]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [hlam, p582_0]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h573, hlam, p582_0]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h575, hlam, p582_0]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p582_1, u4ehi4]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h570, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p582_1, u4ehi4]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h577, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p582_1, u4ehi4]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [hlam, p582_0]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h3, h368, h578, hc02, hc23, hlam, hphi, p582_1]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  rcases p582_3 (m.d 0 4) (by simp) with h597 | h597
                                  · linarith only [h307, h597, hlam]
                                  · linarith only [h570, h597, hlam]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h2, h577, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p582_1, u4ehi4]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h577, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p582_1, u4ehi4]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h578, hlam, p582_0]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [hlam, p582_0]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h578, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p582_1, u4ehi4]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h570, hlam, p582_0]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h577, hlam, p582_0]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h580, hlam, p582_0]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [h581, hlam, p582_0]
                                · obtain ⟨p582_0, p582_1, p582_2, p582_3⟩ := h582c
                                  linarith only [hlam, p582_0]
                              · linarith only [h1, h2, h368, h577, h581, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · linarith only [h2, h368, h577, h578, h580, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                          · linarith only [h2, h368, h577, h578, h579, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h613 | h613
                          · linarith only [h578, h613, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h615 | h615
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h616 | h616
                              · rcases h4bigk with h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [hlam, p617_0]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [h577, hc04, hlam, hphi, ht0b, ht45, ht5b, p617_1, u4ehi4]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [h307, hlam, p617_0]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [h368, hlam, p617_0]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  rcases p617_3 (m.d 0 4) (by simp) with h622 | h622
                                  · rcases p617_3 (m.d 1 4) (by simp) with h623 | h623
                                    · linarith only [h2, h623, hlam]
                                    · linarith only [h577, h623, hlam]
                                  · linarith only [h622, hlam, p617_0]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [h2, hlam, p617_0]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [hlam, p617_0]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [h573, hlam, p617_0]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [h575, hlam, p617_0]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p617_1, u4ehi4]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [h1, h368, h578, hc34, hlam, hphi, p617_1, u3ehi1]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [h575, h578, hc34, hlam, hphi, p617_1, u3ehi1]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [hlam, p617_0]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [h578, hlam, p617_1]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  rcases p617_3 (m.d 0 4) (by simp) with h636 | h636
                                  · linarith only [h307, h636, hlam]
                                  · linarith only [h570, h636, hlam]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [h2, h577, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p617_1, u4ehi4]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [h577, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p617_1, u4ehi4]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [h0, h307, hc12, hc34, hlam, hphi, ht23, p617_1]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [hlam, p617_0]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  rcases p617_3 (m.d 0 4) (by simp) with h643 | h643
                                  · linarith only [h368, h643, hlam]
                                  · linarith only [h570, h643, hlam]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [h570, hlam, p617_0]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [h577, hlam, p617_0]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [h615, hlam, p617_0]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [h616, hlam, p617_0]
                                · obtain ⟨p617_0, p617_1, p617_2, p617_3⟩ := h617c
                                  linarith only [hlam, p617_0]
                              · linarith only [h2, h577, h616, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h2, h307, h577, h615, hlam]
                      · linarith only [h368, h570, h575, h577, hc34, hlam, hphi, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h654 | h654
                · linarith only [h0, h3, h654, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h656 | h656
                  · linarith only [h0, h3, h368, h570, h656, hc45, hlam, hphi, u4ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h658 | h658
                    · linarith only [h1, h368, h570, h658, hc45, hlam, hphi, ht34, u3ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h660 | h660
                      · linarith only [h2, h368, h570, h660, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h662 | h662
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h663 | h663
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h664 | h664
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h665 | h665
                              · linarith only [h1, h368, h570, h665, hc34, hlam, hphi, u3ehi1]
                              · linarith only [h1, h368, h662, h664, h665, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                            · linarith only [h1, h368, h662, h664, hc45, hlam, hphi, ht34, u3ehi1]
                          · linarith only [h1, h368, h662, h663, hc35, hlam, hphi, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h670 | h670
                          · linarith only [h662, h670, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h672 | h672
                            · linarith only [h1, h368, h570, h662, h672, hc34, hlam, hphi, u3ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h674 | h674
                              · linarith only [h1, h307, h368, h672, h674, hc34, hlam, hphi, u3ehi1]
                              · linarith only [h1, h368, h674, hc45, hlam, hphi, ht34, u3ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h677 | h677
        · rcases m.htr 0 2 4 (by decide) (by decide) with h678 | h678
          · linarith only [h0, h2, h678, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h680 | h680
            · linarith only [h1, h2, h680, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h682 | h682
              · rcases m.htr 1 2 3 (by decide) (by decide) with h683 | h683
                · linarith only [h0, h2, h683, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h677, h678, h683, hc12, hc24, hlam, hphi]
              · linarith only [h0, h2, h677, h682, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h687 | h687
          · linarith only [h1, h2, h677, h687, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h689 | h689
            · linarith only [h1, h2, h689, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h691 | h691
              · rcases m.htr 1 2 3 (by decide) (by decide) with h692 | h692
                · linarith only [h0, h2, h677, h692, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h694 | h694
                  · linarith only [h0, h2, h687, h694, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h696 | h696
                    · linarith only [h1, h2, h677, h689, h694, h696, hc02, hc24, hlam, hphi]
                    · linarith only [h1, h2, h696, hc34, hlam, hphi, u3ehi1]
              · linarith only [h1, h2, h691, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h700 | h700
      · rcases m.htr 0 2 3 (by decide) (by decide) with h701 | h701
        · linarith only [h0, h1, h701, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h703 | h703
          · rcases m.htr 0 3 4 (by decide) (by decide) with h704 | h704
            · rcases m.htr 0 4 5 (by decide) (by decide) with h705 | h705
              · rcases m.htr 1 2 3 (by decide) (by decide) with h706 | h706
                · linarith only [h701, h703, h706, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h708 | h708
                  · linarith only [h0, h1, h706, h708, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · linarith only [h0, h1, h703, h706, h708, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h711 | h711
                · linarith only [h0, h1, h711, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h713 | h713
                  · linarith only [h0, h1, h711, h713, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · linarith only [h0, h1, h703, h711, h713, hc12, hc23, hlam, hphi]
            · linarith only [h1, h700, h704, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h717 | h717
            · rcases m.htr 0 4 5 (by decide) (by decide) with h718 | h718
              · rcases m.htr 1 2 3 (by decide) (by decide) with h719 | h719
                · linarith only [h0, h1, h701, h719, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h721 | h721
                  · linarith only [h0, h1, h703, h719, h721, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h723 | h723
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h724 | h724
                      · linarith only [h1, h700, h719, h724, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h1, h700, h718, h719, h721, h724, hc12, hc23, hlam, hphi]
                    · linarith only [h1, h700, h718, h723, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h728 | h728
                · linarith only [h0, h1, h728, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h730 | h730
                  · linarith only [h0, h703, h730, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h732 | h732
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h733 | h733
                      · linarith only [h1, h700, h718, h728, h733, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h735 | h735
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h736 | h736
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h737 | h737
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h738 | h738
                              · linarith only [h700, h718, h732, h738, hlam]
                              · rcases h4bigk with h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [hlam, p740_0]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [h718, h730, h735, h737, hc12, hc23, hlam, hphi, p740_1]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [h703, hlam, p740_0]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [h718, h735, h737, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p740_1, u3ehi3]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [h718, hlam, p740_0]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [h700, hlam, p740_0]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [hlam, p740_0]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [h730, hlam, p740_0]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [h700, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p740_1, u3ehi3]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [h733, hlam, p740_0]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  rcases p740_3 (m.d 0 4) (by simp) with h751 | h751
                                  · linarith only [h703, h751, hlam]
                                  · rcases p740_3 (m.d 1 4) (by simp) with h753 | h753
                                    · linarith only [h730, h753, hlam]
                                    · rcases p740_3 (m.d 2 4) (by simp) with h755 | h755
                                      · rcases p740_3 (m.d 3 4) (by simp) with h756 | h756
                                        · linarith only [h735, h756, hlam]
                                        · rcases p740_3 (m.d 4 5) (by simp) with h758 | h758
                                          · linarith only [h737, h758, hlam]
                                          · linarith only [h718, h758, hlam]
                                      · linarith only [h703, h755, hlam]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  rcases p740_3 (m.d 0 4) (by simp) with h762 | h762
                                  · linarith only [h703, h762, hlam]
                                  · linarith only [h700, h762, hlam]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [hlam, p740_0]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  rcases p740_3 (m.d 0 4) (by simp) with h766 | h766
                                  · linarith only [h703, h766, hlam]
                                  · linarith only [h717, h766, hlam]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [h718, h735, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p740_1, u4ehi0]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [h717, hlam, p740_1]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [h732, hlam, p740_1]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [h735, hlam, p740_0]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [hlam, p740_0]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [h738, hlam, p740_0]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [h700, hc45, hlam, hphi, p740_1, u4ehi1]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [h732, hc45, hlam, hphi, ht34, p740_1, u3ehi3]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [h737, hlam, p740_0]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [h735, h737, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p740_1, u3ehi3]
                                · obtain ⟨p740_0, p740_1, p740_2, p740_3⟩ := h740c
                                  linarith only [hlam, p740_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h780 | h780
                              · linarith only [h0, h703, h737, h780, hc12, hc34, hlam, hphi, ht23]
                              · rcases h4bigk with h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [hlam, p782_0]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h703, h732, h737, hc45, hlam, hphi, ht34, p782_1, u3ehi3]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h703, hlam, p782_0]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h703, h737, hc45, hlam, hphi, ht34, p782_1, u3ehi3]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h718, hlam, p782_0]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h700, hlam, p782_0]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [hlam, p782_0]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h730, hlam, p782_0]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h1, h700, h728, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p782_1, u3ehi3]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h733, hlam, p782_0]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h737, hc45, hlam, hphi, p782_1, u4ehi0]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h737, hc45, hlam, hphi, p782_1, u4ehi1]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [hlam, p782_0]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h737, hc45, hlam, hphi, ht34, p782_1, u3ehi3]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h737, hlam, p782_0]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h717, hlam, p782_1]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h732, hlam, p782_1]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h735, hlam, p782_0]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [hlam, p782_0]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h780, hlam, p782_0]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h700, h732, hc45, hlam, hphi, ht34, p782_1, u3ehi3]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [h732, hc45, hlam, hphi, ht34, p782_1, u3ehi3]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [hc45, hlam, hphi, p782_1, u4ehi2]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [hc45, hlam, hphi, ht34, p782_1, u3ehi3]
                                · obtain ⟨p782_0, p782_1, p782_2, p782_3⟩ := h782c
                                  linarith only [hlam, p782_0]
                          · linarith only [h0, h1, h728, h736, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h700, h728, h732, h735, hlam]
                    · linarith only [h1, h700, h732, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
            · linarith only [h1, h700, h717, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h812 | h812
        · linarith only [h0, h1, h812, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h814 | h814
          · linarith only [h0, h700, h814, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h816 | h816
            · rcases m.htr 0 4 5 (by decide) (by decide) with h817 | h817
              · rcases m.htr 1 2 3 (by decide) (by decide) with h818 | h818
                · linarith only [h0, h1, h812, h818, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h820 | h820
                  · linarith only [h0, h700, h814, h820, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h822 | h822
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h823 | h823
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h824 | h824
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h825 | h825
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h826 | h826
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h827 | h827
                              · rcases h4bigk with h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [hlam, p828_0]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [h700, hlam, p828_1]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [h814, hlam, p828_0]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [h827, hc04, hlam, hphi, ht0b, ht45, ht5b, p828_1, u4ehi4]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  rcases p828_3 (m.d 0 4) (by simp) with h833 | h833
                                  · rcases p828_3 (m.d 1 4) (by simp) with h834 | h834
                                    · rcases p828_3 (m.d 2 4) (by simp) with h835 | h835
                                      · rcases p828_3 (m.d 3 4) (by simp) with h836 | h836
                                        · linarith only [h816, h836, hlam]
                                        · linarith only [h827, h836, hlam]
                                      · linarith only [h826, h835, hlam]
                                    · linarith only [h823, h834, hlam]
                                  · linarith only [h833, hlam, p828_0]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [h0, h700, h818, h822, hc12, hc23, hlam, hphi, p828_1]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [hlam, p828_0]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [h820, hlam, p828_0]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [h818, h822, h827, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p828_1, u4ehi4]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  rcases p828_3 (m.d 0 4) (by simp) with h846 | h846
                                  · linarith only [h700, h846, hlam]
                                  · linarith only [h817, h846, hlam]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [h816, h827, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p828_1, u4ehi4]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [h0, h700, hc12, hc24, hlam, hphi, p828_1]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [hlam, p828_0]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [h824, h827, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p828_1, u4ehi4]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  rcases p828_3 (m.d 0 4) (by simp) with h853 | h853
                                  · linarith only [h814, h853, hlam]
                                  · linarith only [h817, h853, hlam]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [h816, hlam, p828_1]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [h822, hlam, p828_1]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [h824, hlam, p828_0]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [hlam, p828_0]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [h816, hc03, hlam, hphi, ht0b, ht45, ht5b, p828_1, u4ehi4]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [h817, hlam, p828_0]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [h823, hlam, p828_0]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [h826, hlam, p828_0]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [h827, hlam, p828_0]
                                · obtain ⟨p828_0, p828_1, p828_2, p828_3⟩ := h828c
                                  linarith only [hlam, p828_0]
                              · rcases h4bigk with h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [hlam, p866_0]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [h700, hlam, p866_1]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [h814, hlam, p866_0]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  rcases p866_3 (m.d 0 4) (by simp) with h870 | h870
                                  · rcases p866_3 (m.d 1 4) (by simp) with h871 | h871
                                    · rcases p866_3 (m.d 2 4) (by simp) with h872 | h872
                                      · rcases p866_3 (m.d 3 4) (by simp) with h873 | h873
                                        · linarith only [h816, h873, hlam]
                                        · rcases p866_3 (m.d 4 5) (by simp) with h875 | h875
                                          · linarith only [h817, h875, hlam]
                                          · linarith only [h827, h875, hlam]
                                      · linarith only [h824, h872, hlam]
                                    · linarith only [h822, h871, hlam]
                                  · linarith only [h816, h870, hlam]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [h827, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p866_1, u3ehi3]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [h817, h827, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p866_1, u3ehi3]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [hlam, p866_0]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [h820, hlam, p866_0]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  rcases p866_3 (m.d 0 4) (by simp) with h885 | h885
                                  · linarith only [h700, h885, hlam]
                                  · linarith only [h816, h885, hlam]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [h820, h824, h827, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p866_1, u3ehi3]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [h817, h824, h827, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p866_1, u3ehi3]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [h700, h824, hc01, hc23, hlam, hphi, ht12, p866_1]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [hlam, p866_0]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  rcases p866_3 (m.d 0 4) (by simp) with h892 | h892
                                  · linarith only [h814, h892, hlam]
                                  · linarith only [h816, h892, hlam]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [h824, h827, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p866_1, u3ehi3]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [h816, hlam, p866_1]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [h822, hlam, p866_1]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [h824, hlam, p866_0]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [hlam, p866_0]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [h827, hlam, p866_0]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [h817, hlam, p866_0]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [h823, hlam, p866_0]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [h826, hlam, p866_0]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [h817, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p866_1, u3ehi3]
                                · obtain ⟨p866_0, p866_1, p866_2, p866_3⟩ := h866c
                                  linarith only [hlam, p866_0]
                            · linarith only [h0, h1, h700, h816, h817, h818, h820, h826, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h818, h825, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h818, h824, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h700, h816, h817, h823, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h1, h816, h822, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h911 | h911
                · linarith only [h0, h700, h911, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h913 | h913
                  · linarith only [h0, h700, h817, h913, hc45, hlam, hphi, u4ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h915 | h915
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h916 | h916
                      · linarith only [h0, h700, h817, h911, h915, h916, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h700, h916, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h0, h1, h816, h915, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h920 | h920
              · rcases m.htr 1 2 3 (by decide) (by decide) with h921 | h921
                · linarith only [h0, h700, h921, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h923 | h923
                  · linarith only [h0, h1, h923, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h925 | h925
                    · linarith only [h0, h1, h816, h921, h925, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h925, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h928 | h928
                · linarith only [h0, h1, h928, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h930 | h930
                  · linarith only [h0, h1, h930, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h932 | h932
                    · linarith only [h0, h1, h816, h928, h932, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h932, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h935 | h935
    · rcases m.htr 0 1 4 (by decide) (by decide) with h936 | h936
      · rcases m.htr 0 2 3 (by decide) (by decide) with h937 | h937
        · rcases m.htr 0 2 4 (by decide) (by decide) with h938 | h938
          · rcases m.htr 0 3 4 (by decide) (by decide) with h939 | h939
            · rcases m.htr 0 4 5 (by decide) (by decide) with h940 | h940
              · rcases m.htr 1 2 3 (by decide) (by decide) with h941 | h941
                · rcases m.htr 1 2 4 (by decide) (by decide) with h942 | h942
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h943 | h943
                    · linarith only [h0, h935, h943, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h935, h939, h943, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h0, h936, h942, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h936, h941, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h948 | h948
                · rcases m.htr 1 2 4 (by decide) (by decide) with h949 | h949
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h950 | h950
                    · linarith only [h0, h935, h950, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h935, h939, h948, h950, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h935, h939, h949, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · linarith only [h0, h935, h939, h948, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h955 | h955
              · rcases m.htr 1 2 3 (by decide) (by decide) with h956 | h956
                · rcases m.htr 1 2 4 (by decide) (by decide) with h957 | h957
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h958 | h958
                    · linarith only [h935, h939, h958, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h960 | h960
                      · linarith only [h0, h936, h960, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h936, h955, h957, h960, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h0, h936, h955, h957, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · linarith only [h0, h936, h955, h956, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h965 | h965
                · rcases m.htr 1 2 4 (by decide) (by decide) with h966 | h966
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h967 | h967
                    · linarith only [h0, h935, h967, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h969 | h969
                      · linarith only [h0, h936, h939, h955, h969, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h971 | h971
                        · linarith only [h935, h939, h965, h971, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h973 | h973
                          · linarith only [h935, h939, h965, h973, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h975 | h975
                            · linarith only [h0, h936, h939, h955, h966, h975, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h977 | h977
                              · linarith only [h935, h939, h955, h965, h977, hc34, hlam, hphi, u3ehi2]
                              · linarith only [h935, h939, h965, h977, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h0, h935, h965, h966, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h935, h965, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h936, h938, hlam]
        · linarith only [h0, h935, h937, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h984 | h984
        · rcases m.htr 0 2 4 (by decide) (by decide) with h985 | h985
          · rcases m.htr 0 3 4 (by decide) (by decide) with h986 | h986
            · linarith only [h935, h936, h986, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h988 | h988
              · rcases m.htr 1 2 3 (by decide) (by decide) with h989 | h989
                · rcases m.htr 1 2 4 (by decide) (by decide) with h990 | h990
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h991 | h991
                    · linarith only [h935, h986, h991, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h935, h936, h989, h991, hc34, hlam, hphi, u3ehi2]
                  · linarith only [h0, h985, h990, hlam]
                · linarith only [h0, h935, h989, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h935, h936, h988, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h997 | h997
            · linarith only [h0, h935, h985, h997, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h999 | h999
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1000 | h1000
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1001 | h1001
                  · linarith only [h0, h1000, h1001, h935, h985, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1000, h1001, h935, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h1000, h935, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h0, h935, h985, h999, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h0, h935, h984, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h1007 | h1007
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1008 | h1008
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1009 | h1009
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1010 | h1010
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1011 | h1011
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1012 | h1012
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1013 | h1013
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1014 | h1014
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1015 | h1015
                      · linarith only [h1007, h1012, h1015, h935, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · linarith only [h1007, h1011, h1012, h1014, h1015, h935, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h1007, h1011, h1014, h935, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · linarith only [h0, h1007, h1011, h1013, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h0, h1007, h1011, h1012, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1021 | h1021
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1022 | h1022
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1023 | h1023
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1024 | h1024
                      · linarith only [h1007, h1011, h1021, h1024, h935, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1026 | h1026
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1027 | h1027
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1028 | h1028
                            · linarith only [h1007, h1011, h1022, h1028, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1030 | h1030
                              · linarith only [h1007, h1011, h1022, h1026, h1030, hlam]
                              · rcases h4bigk with h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [hlam, p1032_0]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1011, h1022, h1026, hc45, hlam, hphi, ht34, p1032_1, u3ehi3]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1011, h1026, hc45, hlam, hphi, ht34, p1032_1, u3ehi3]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1011, hc45, hlam, hphi, ht34, p1032_1, u3ehi3]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1011, hlam, p1032_0]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1007, hlam, p1032_0]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [hlam, p1032_0]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1007, h1021, h1026, h935, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1032_1, u3ehi3]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1007, h1021, h935, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1032_1, u3ehi3]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1024, hlam, p1032_0]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1009, hlam, p1032_1]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1022, hlam, p1032_1]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [hlam, p1032_0]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1009, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1032_1, u3ehi3]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1028, hlam, p1032_0]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1010, hlam, p1032_1]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1023, hlam, p1032_1]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1026, hlam, p1032_0]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [hlam, p1032_0]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1030, hlam, p1032_0]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [hc45, hlam, hphi, p1032_1, u4ehi0]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1023, hc45, hlam, hphi, ht34, p1032_1, u3ehi3]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [h1026, hc45, hlam, hphi, ht34, p1032_1, u3ehi3]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [hc45, hlam, hphi, ht34, p1032_1, u3ehi3]
                                · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                  linarith only [hlam, p1032_0]
                          · linarith only [h1026, h1027, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1010, h1011, h1026, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h1010, h1011, h1023, h935, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h1007, h1021, h1022, h935, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h1007, h1021, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h1007, h1010, h935, hlam]
          · linarith only [h1007, h1008, h1009, h935, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1065 | h1065
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1066 | h1066
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1067 | h1067
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1068 | h1068
                · linarith only [h1008, h1065, h1068, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h0, h1007, h1067, h1068, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1071 | h1071
                · linarith only [h0, h1007, h1008, h1071, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h0, h1007, h1071, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h1007, h1008, h1066, hlam]
          · linarith only [h0, h1007, h1065, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1076 | h1076
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1077 | h1077
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1078 | h1078
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1079 | h1079
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1080 | h1080
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1081 | h1081
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1082 | h1082
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1083 | h1083
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1084 | h1084
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1085 | h1085
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1086 | h1086
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1087 | h1087
                              · linarith only [h1076, h1084, h1087, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h0, h1076, h1084, h1086, h1087, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1090 | h1090
                              · linarith only [h1084, h1086, h1090, hlam]
                              · rcases h4bigk with h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [hlam, p1092_0]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [h1007, hlam, p1092_1]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  rcases p1092_3 (m.d 0 4) (by simp) with h1095 | h1095
                                  · rcases p1092_3 (m.d 1 4) (by simp) with h1096 | h1096
                                    · rcases p1092_3 (m.d 2 4) (by simp) with h1097 | h1097
                                      · linarith only [h1077, h1097, hlam]
                                      · rcases p1092_3 (m.d 3 4) (by simp) with h1099 | h1099
                                        · linarith only [h1078, h1099, hlam]
                                        · rcases p1092_3 (m.d 4 5) (by simp) with h1101 | h1101
                                          · linarith only [h1079, h1101, hlam]
                                          · linarith only [h1086, h1101, hlam]
                                    · linarith only [h1081, h1096, hlam]
                                  · linarith only [h1077, h1095, hlam]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  rcases p1092_3 (m.d 0 4) (by simp) with h1106 | h1106
                                  · rcases p1092_3 (m.d 1 4) (by simp) with h1107 | h1107
                                    · rcases p1092_3 (m.d 2 4) (by simp) with h1108 | h1108
                                      · linarith only [h1077, h1108, hlam]
                                      · linarith only [h1084, h1108, hlam]
                                    · linarith only [h1082, h1107, hlam]
                                  · linarith only [h1078, h1106, hlam]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [h1078, h1084, h1086, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1092_1, u3ehi3]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [h1079, h1080, h1082, h1084, h1086, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1092_1, u3ehi3]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [hlam, p1092_0]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  rcases p1092_3 (m.d 0 4) (by simp) with h1116 | h1116
                                  · linarith only [h1007, h1116, hlam]
                                  · linarith only [h1077, h1116, hlam]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  rcases p1092_3 (m.d 0 4) (by simp) with h1119 | h1119
                                  · linarith only [h1007, h1119, hlam]
                                  · linarith only [h1078, h1119, hlam]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [h1080, h1082, h1084, h1086, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1092_1, u3ehi3]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [h1077, hlam, p1092_1]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [h1081, hlam, p1092_1]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [hlam, p1092_0]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [h1079, h1086, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1092_1, u3ehi3]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [h1086, hlam, p1092_0]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [h1078, hlam, p1092_1]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [h1082, hlam, p1092_1]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [h1084, hlam, p1092_0]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [hlam, p1092_0]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [h1090, hlam, p1092_0]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [h1079, hlam, p1092_0]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [h1083, hlam, p1092_0]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [h1079, hc04, hlam, hphi, ht0b, ht45, ht5b, p1092_1, u4ehi2]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [h1007, h1079, h1080, h1082, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1092_1, u3ehi3]
                                · obtain ⟨p1092_0, p1092_1, p1092_2, p1092_3⟩ := h1092c
                                  linarith only [hlam, p1092_0]
                          · linarith only [h1084, h1085, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1139 | h1139
                          · linarith only [h1084, h1139, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1141 | h1141
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1142 | h1142
                              · rcases h4bigk with h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [hlam, p1143_0]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h1007, hlam, p1143_1]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h1007, h1080, h1082, h1141, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1143_1, u4ehi4]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h1007, h1080, h1082, h1139, h1142, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1143_1, u3ehi2]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  rcases p1143_3 (m.d 0 4) (by simp) with h1148 | h1148
                                  · rcases p1143_3 (m.d 1 4) (by simp) with h1149 | h1149
                                    · rcases p1143_3 (m.d 2 4) (by simp) with h1150 | h1150
                                      · linarith only [h1077, h1150, hlam]
                                      · linarith only [h1141, h1150, hlam]
                                    · linarith only [h1083, h1149, hlam]
                                  · linarith only [h1148, hlam, p1143_0]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h1077, h1080, h1082, h1141, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1143_1, u4ehi4]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [hlam, p1143_0]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h1080, h1082, h1141, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1143_1, u4ehi4]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h1080, h1082, h1139, h1142, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1143_1, u3ehi2]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  rcases p1143_3 (m.d 0 4) (by simp) with h1159 | h1159
                                  · linarith only [h1007, h1159, hlam]
                                  · linarith only [h1079, h1159, hlam]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h1077, hlam, p1143_1]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h1081, hlam, p1143_1]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [hlam, p1143_0]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h1084, hlam, p1143_1]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h0, h1077, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1143_1, u4ehi4]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h1078, hlam, p1143_1]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h1082, hlam, p1143_1]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h1078, h1080, h935, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1143_1, u4ehi2]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [hlam, p1143_0]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h1078, h1080, h935, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1143_1, u4ehi4]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h1079, hlam, p1143_0]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h1083, hlam, p1143_0]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h1141, hlam, p1143_0]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [h1142, hlam, p1143_0]
                                · obtain ⟨p1143_0, p1143_1, p1143_2, p1143_3⟩ := h1143c
                                  linarith only [hlam, p1143_0]
                              · linarith only [h0, h1077, h1141, h1142, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1178 | h1178
                              · linarith only [h1078, h1080, h1141, h1178, h935, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                              · linarith only [h1007, h1079, h1080, h1082, h1084, h1178, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h1007, h1079, h1083, hlam]
                    · linarith only [h1078, h1082, h935, hlam]
                  · linarith only [h0, h1077, h1081, hlam]
                · linarith only [h0, h1076, h1080, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1185 | h1185
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1186 | h1186
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1187 | h1187
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1188 | h1188
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1189 | h1189
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1190 | h1190
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1191 | h1191
                            · linarith only [h1077, h1079, h1191, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1193 | h1193
                              · linarith only [h1077, h1079, h1189, h1193, hlam]
                              · rcases h4bigk with h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [hlam, p1195_0]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [h1007, hlam, p1195_1]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [h1079, h1185, h1187, h1188, h1189, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1195_1, u3ehi3]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [h1079, h1185, h1187, h1188, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1195_1, u3ehi3]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [h1079, hlam, p1195_0]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  rcases p1195_3 (m.d 0 4) (by simp) with h1201 | h1201
                                  · linarith only [h1007, h1201, hlam]
                                  · rcases p1195_3 (m.d 1 4) (by simp) with h1203 | h1203
                                    · rcases p1195_3 (m.d 2 4) (by simp) with h1204 | h1204
                                      · linarith only [h1186, h1204, hlam]
                                      · rcases p1195_3 (m.d 3 4) (by simp) with h1206 | h1206
                                        · linarith only [h1187, h1206, hlam]
                                        · rcases p1195_3 (m.d 4 5) (by simp) with h1208 | h1208
                                          · linarith only [h1188, h1208, hlam]
                                          · linarith only [h1079, h1208, hlam]
                                    · linarith only [h1007, h1203, hlam]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [hlam, p1195_0]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  rcases p1195_3 (m.d 0 4) (by simp) with h1213 | h1213
                                  · linarith only [h1007, h1213, hlam]
                                  · linarith only [h1077, h1213, hlam]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  rcases p1195_3 (m.d 0 4) (by simp) with h1216 | h1216
                                  · linarith only [h1007, h1216, hlam]
                                  · linarith only [h1078, h1216, hlam]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [h1079, h1185, h1187, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1195_1, u4ehi0]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [h1077, hlam, p1195_1]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [h1186, hlam, p1195_1]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [hlam, p1195_0]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [h0, h1077, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1195_1, u3ehi3]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [h1191, hlam, p1195_0]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [h1078, hlam, p1195_1]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [h1187, hlam, p1195_1]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [h1189, hlam, p1195_0]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [hlam, p1195_0]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [h1193, hlam, p1195_0]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [hc45, hlam, hphi, p1195_1, u4ehi0]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [h1188, hlam, p1195_0]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [h1185, h1187, h1188, h1189, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1195_1, u3ehi3]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [h1185, h1187, h1188, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1195_1, u3ehi3]
                                · obtain ⟨p1195_0, p1195_1, p1195_2, p1195_3⟩ := h1195c
                                  linarith only [hlam, p1195_0]
                          · linarith only [h1189, h1190, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1078, h1079, h1185, h1187, h1188, h1189, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1237 | h1237
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1238 | h1238
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1239 | h1239
                            · linarith only [h1007, h1077, h1188, h1239, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1241 | h1241
                              · linarith only [h0, h1007, h1076, h1188, h1237, h1241, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                              · rcases h4bigk with h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [hlam, p1243_0]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [h1007, hlam, p1243_1]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [h1007, h1188, h1237, hc45, hlam, hphi, ht34, p1243_1, u3ehi3]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [h1007, h1188, hc45, hlam, hphi, ht34, p1243_1, u3ehi3]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [h1079, hlam, p1243_0]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [h1188, hc45, hlam, hphi, p1243_1, u4ehi0]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [hlam, p1243_0]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [h1188, h1237, hc45, hlam, hphi, ht34, p1243_1, u3ehi3]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [h1188, hc45, hlam, hphi, ht34, p1243_1, u3ehi3]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [h1188, hlam, p1243_0]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [h1077, hlam, p1243_1]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [h1186, hlam, p1243_1]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [hlam, p1243_0]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [h1007, h1077, h1188, hc45, hlam, hphi, ht34, p1243_1, u3ehi3]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [h1239, hlam, p1243_0]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [h1078, hlam, p1243_1]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [h1187, hlam, p1243_1]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [h1237, hlam, p1243_0]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [hlam, p1243_0]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [h1241, hlam, p1243_0]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [hc45, hlam, hphi, p1243_1, u4ehi0]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [hc45, hlam, hphi, p1243_1, u4ehi1]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [h1237, hc45, hlam, hphi, ht34, p1243_1, u3ehi3]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [hc45, hlam, hphi, ht34, p1243_1, u3ehi3]
                                · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                  linarith only [hlam, p1243_0]
                          · linarith only [h1237, h1238, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1078, h1079, h1237, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h1078, h1079, h1187, hc45, hlam, hphi, ht34, u3ehi1]
                  · linarith only [h0, h1076, h1077, h1079, h1186, hc45, hlam, hphi, ht34, u3ehi0]
                · linarith only [h0, h1076, h1185, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1274 | h1274
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1275 | h1275
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1276 | h1276
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1277 | h1277
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1278 | h1278
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1279 | h1279
                        · linarith only [h1076, h1078, h1279, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1281 | h1281
                          · linarith only [h1076, h1078, h1275, h1277, h1281, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1283 | h1283
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1284 | h1284
                              · rcases h4bigk with h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [hlam, p1285_0]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1007, hlam, p1285_1]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1078, h1275, h1277, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1285_1, u4ehi2]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1078, hlam, p1285_0]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1078, h1275, h1277, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1285_1, u4ehi4]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1077, h1283, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1285_1, u4ehi4]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [hlam, p1285_0]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1276, h1283, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1285_1, u4ehi4]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1078, h1275, h1277, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1285_1, u3ehi0]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  rcases p1285_3 (m.d 0 4) (by simp) with h1295 | h1295
                                  · linarith only [h1007, h1295, hlam]
                                  · linarith only [h1274, h1295, hlam]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1077, hlam, p1285_1]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1276, hlam, p1285_1]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [hlam, p1285_0]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1279, hlam, p1285_1]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h0, h1077, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1285_1, u4ehi4]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1076, h1078, hc34, hlam, hphi, p1285_1, u3ehi2]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1277, hlam, p1285_1]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1275, h1277, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1285_1, u4ehi2]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [hlam, p1285_0]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1275, h1277, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1285_1, u4ehi4]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1274, hlam, p1285_0]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1278, hlam, p1285_0]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1283, hlam, p1285_0]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [h1284, hlam, p1285_0]
                                · obtain ⟨p1285_0, p1285_1, p1285_2, p1285_3⟩ := h1285c
                                  linarith only [hlam, p1285_0]
                              · linarith only [h1076, h1077, h1078, h1283, h1284, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h1078, h1274, h1275, h1277, h1283, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h1078, h1274, h1275, h1277, h1278, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1316 | h1316
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1317 | h1317
                        · linarith only [h1277, h1317, h935, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1319 | h1319
                          · linarith only [h1076, h1078, h1319, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1321 | h1321
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1322 | h1322
                              · rcases h4bigk with h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c | h1323c
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [hlam, p1323_0]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [h1007, hlam, p1323_1]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [h1007, h1277, h1321, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1323_1, u5ehi4]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [h1078, hlam, p1323_0]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  rcases p1323_3 (m.d 0 4) (by simp) with h1328 | h1328
                                  · rcases p1323_3 (m.d 1 4) (by simp) with h1329 | h1329
                                    · rcases p1323_3 (m.d 2 4) (by simp) with h1330 | h1330
                                      · linarith only [h1077, h1330, hlam]
                                      · linarith only [h1321, h1330, hlam]
                                    · linarith only [h1316, h1329, hlam]
                                  · linarith only [h1328, hlam, p1323_0]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [h1077, h1277, h1321, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1323_1, u4ehi4]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [hlam, p1323_0]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [h1277, h1321, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1323_1, u4ehi4]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [h1277, hlam, p1323_0]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  rcases p1323_3 (m.d 0 4) (by simp) with h1339 | h1339
                                  · linarith only [h1007, h1339, hlam]
                                  · linarith only [h1274, h1339, hlam]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [h1077, hlam, p1323_1]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [h1276, hlam, p1323_1]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [hlam, p1323_0]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [h1317, hlam, p1323_1]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [h0, h1077, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1323_1, u4ehi4]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [h1078, hc34, hlam, hphi, p1323_1, u3ehi0]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [h1007, hc01, hc34, hlam, hphi, ht12, ht23, p1323_1]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [h1317, hc34, hlam, hphi, p1323_1, u3ehi2]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [hlam, p1323_0]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  rcases p1323_3 (m.d 0 4) (by simp) with h1351 | h1351
                                  · linarith only [h1078, h1351, hlam]
                                  · linarith only [h1274, h1351, hlam]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [h1274, hlam, p1323_0]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [h1316, hlam, p1323_0]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [h1321, hlam, p1323_0]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [h1322, hlam, p1323_0]
                                · obtain ⟨p1323_0, p1323_1, p1323_2, p1323_3⟩ := h1323c
                                  linarith only [hlam, p1323_0]
                              · linarith only [h0, h1077, h1321, h1322, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1007, h1274, h1277, h1317, h1321, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h1007, h1274, h1316, hlam]
                  · linarith only [h0, h1077, h1276, hlam]
                · linarith only [h0, h1076, h1077, h1078, h1275, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1364 | h1364
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1365 | h1365
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1366 | h1366
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1367 | h1367
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1368 | h1368
                        · linarith only [h1076, h1078, h1368, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1370 | h1370
                          · linarith only [h1076, h1078, h1274, h1364, h1366, h1367, h1370, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1372 | h1372
                            · linarith only [h1076, h1077, h1078, h1274, h1372, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1374 | h1374
                              · linarith only [h1076, h1078, h1274, h1374, hc34, hlam, hphi, u3ehi2]
                              · linarith only [h1076, h1078, h1364, h1366, h1367, h1374, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h1076, h1078, h1366, h1367, hc45, hlam, hphi, ht34, u3ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1378 | h1378
                      · linarith only [h1076, h1078, h1274, h1366, h1378, hc34, hlam, hphi, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1380 | h1380
                        · linarith only [h1076, h1366, h1378, h1380, h935, hc45, hlam, hphi, ht34, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1382 | h1382
                          · linarith only [h1076, h1366, h1378, h1382, h935, hc45, hlam, hphi, ht34, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1384 | h1384
                            · linarith only [h1366, h1378, h1384, h935, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1386 | h1386
                              · linarith only [h1366, h1378, h1386, h935, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h1076, h1078, h1386, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h0, h1077, h1365, hlam]
                · linarith only [h0, h1076, h1364, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1391 | h1391
            · linarith only [h1076, h1077, h1391, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1393 | h1393
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1394 | h1394
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1395 | h1395
                  · linarith only [h1076, h1077, h1395, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1397 | h1397
                    · linarith only [h1076, h1077, h1391, h1394, h1395, h1397, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1399 | h1399
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1400 | h1400
                        · linarith only [h1076, h1397, h1400, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h0, h1076, h1395, h1400, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h1007, h1076, h1077, h1399, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h0, h1076, h1394, hlam]
              · linarith only [h1076, h1077, h1393, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1406 | h1406
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1407 | h1407
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1408 | h1408
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1409 | h1409
                · linarith only [h1076, h1406, h1409, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1411 | h1411
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1412 | h1412
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1413 | h1413
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1414 | h1414
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1415 | h1415
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1416 | h1416
                            · linarith only [h1076, h1406, h1416, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · linarith only [h1007, h1408, h1409, h1411, h1416, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                          · linarith only [h1007, h1408, h1409, h1411, h1415, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · linarith only [h1007, h1407, h1408, h1409, h1411, h1414, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h1007, h1408, h1413, hlam]
                    · linarith only [h1076, h1406, h1407, h1412, h935, hlam]
                  · linarith only [h0, h1076, h1406, h1411, h935, hc01, hc13, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1424 | h1424
                · linarith only [h1076, h1406, h1424, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1426 | h1426
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1427 | h1427
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1428 | h1428
                      · linarith only [h1408, h1424, h1426, h1428, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1430 | h1430
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1431 | h1431
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1432 | h1432
                            · linarith only [h1406, h1428, h1432, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1434 | h1434
                              · linarith only [h1007, h1428, h1434, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases h4bigk with h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [hlam, p1436_0]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [h1007, hlam, p1436_1]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [h1007, h1428, hc45, hlam, hphi, p1436_1, u4ehi2]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [h1007, h1428, hc45, hlam, hphi, ht34, p1436_1, u3ehi3]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [h1408, hlam, p1436_0]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [h1428, hc45, hlam, hphi, p1436_1, u4ehi0]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [hlam, p1436_0]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [h1428, h1430, hc45, hlam, hphi, ht34, p1436_1, u3ehi3]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [h1428, hc45, hlam, hphi, ht34, p1436_1, u3ehi3]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [h1428, hlam, p1436_0]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [h1406, hlam, p1436_1]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [h1426, hlam, p1436_1]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [hlam, p1436_0]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [h0, h1406, h1424, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1436_1, u3ehi3]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [h1432, hlam, p1436_0]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [h1407, hlam, p1436_1]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [h1427, hlam, p1436_1]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [h1430, hlam, p1436_0]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [hlam, p1436_0]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [h1434, hlam, p1436_0]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [hc45, hlam, hphi, p1436_1, u4ehi0]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [hc45, hlam, hphi, p1436_1, u4ehi1]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [h1430, hc45, hlam, hphi, ht34, p1436_1, u3ehi3]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [hc45, hlam, hphi, ht34, p1436_1, u3ehi3]
                                · obtain ⟨p1436_0, p1436_1, p1436_2, p1436_3⟩ := h1436c
                                  linarith only [hlam, p1436_0]
                          · linarith only [h0, h1424, h1431, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h1406, h1407, h1424, h1430, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h1076, h1406, h1407, h1427, h935, hlam]
                  · linarith only [h0, h1406, h1426, hlam]
            · linarith only [h1076, h1406, h1407, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1467 | h1467
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1468 | h1468
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1469 | h1469
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1470 | h1470
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1471 | h1471
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1472 | h1472
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1473 | h1473
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1474 | h1474
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1475 | h1475
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1476 | h1476
                              · linarith only [h1076, h1467, h1469, h1476, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h1406, h1468, h1469, h1473, h1476, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1406, h1468, h1475, hlam]
                          · linarith only [h1076, h1467, h1474, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1076, h1467, h1473, hlam]
                      · linarith only [h1406, h1468, h1470, h1472, hlam]
                    · linarith only [h1076, h1467, h1469, h1471, hlam]
                  · linarith only [h1076, h1467, h1469, h1470, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1485 | h1485
                  · linarith only [h1406, h1469, h1485, hc02, hc23, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1487 | h1487
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1488 | h1488
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1489 | h1489
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1490 | h1490
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1491 | h1491
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1492 | h1492
                              · rcases h4bigk with h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [hlam, p1493_0]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [h1007, hlam, p1493_1]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [h1406, hlam, p1493_0]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [h1467, h1492, hc03, hlam, hphi, ht0b, ht45, ht5b, p1493_1, u4ehi4]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  rcases p1493_3 (m.d 0 4) (by simp) with h1498 | h1498
                                  · rcases p1493_3 (m.d 1 4) (by simp) with h1499 | h1499
                                    · rcases p1493_3 (m.d 2 4) (by simp) with h1500 | h1500
                                      · rcases p1493_3 (m.d 3 4) (by simp) with h1501 | h1501
                                        · linarith only [h1467, h1501, hlam]
                                        · linarith only [h1492, h1501, hlam]
                                      · linarith only [h1491, h1500, hlam]
                                    · linarith only [h1488, h1499, hlam]
                                  · linarith only [h1498, hlam, p1493_0]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [h1467, h1469, h1487, h1492, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1493_1, u4ehi4]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [hlam, p1493_0]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [h1485, hlam, p1493_0]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [h1469, h1487, h1492, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1493_1, u4ehi4]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  rcases p1493_3 (m.d 0 4) (by simp) with h1511 | h1511
                                  · linarith only [h1007, h1511, hlam]
                                  · linarith only [h1468, h1511, hlam]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [h1467, h1489, h1492, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1493_1, u4ehi4]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [h1007, h1489, hc01, hc23, hlam, hphi, ht12, p1493_1]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [hlam, p1493_0]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [h1489, h1492, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1493_1, u4ehi4]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  rcases p1493_3 (m.d 0 4) (by simp) with h1518 | h1518
                                  · linarith only [h1406, h1518, hlam]
                                  · linarith only [h1468, h1518, hlam]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [h1467, hlam, p1493_1]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [h1487, hlam, p1493_1]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [h1489, hlam, p1493_0]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [hlam, p1493_0]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [h1467, h1469, h935, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1493_1, u4ehi4]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [h1468, hlam, p1493_0]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [h1488, hlam, p1493_0]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [h1491, hlam, p1493_0]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [h1492, hlam, p1493_0]
                                · obtain ⟨p1493_0, p1493_1, p1493_2, p1493_3⟩ := h1493c
                                  linarith only [hlam, p1493_0]
                              · rcases h4bigk with h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [hlam, p1531_0]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [h1007, hlam, p1531_1]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [h1406, hlam, p1531_0]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  rcases p1531_3 (m.d 0 4) (by simp) with h1535 | h1535
                                  · rcases p1531_3 (m.d 1 4) (by simp) with h1536 | h1536
                                    · rcases p1531_3 (m.d 2 4) (by simp) with h1537 | h1537
                                      · rcases p1531_3 (m.d 3 4) (by simp) with h1538 | h1538
                                        · linarith only [h1467, h1538, hlam]
                                        · rcases p1531_3 (m.d 4 5) (by simp) with h1540 | h1540
                                          · linarith only [h1468, h1540, hlam]
                                          · linarith only [h1492, h1540, hlam]
                                      · linarith only [h1489, h1537, hlam]
                                    · linarith only [h1487, h1536, hlam]
                                  · linarith only [h1467, h1535, hlam]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [h1467, h1469, h1492, h935, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1531_1, u3ehi3]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [h1468, h1485, h1489, h1492, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1531_1, u3ehi3]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [hlam, p1531_0]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [h1485, hlam, p1531_0]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  rcases p1531_3 (m.d 0 4) (by simp) with h1550 | h1550
                                  · linarith only [h1007, h1550, hlam]
                                  · linarith only [h1467, h1550, hlam]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [h1485, h1489, h1492, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1531_1, u3ehi3]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [h1468, h1489, h1492, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1531_1, u3ehi3]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [h1007, h1489, hc01, hc23, hlam, hphi, ht12, p1531_1]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [hlam, p1531_0]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  rcases p1531_3 (m.d 0 4) (by simp) with h1557 | h1557
                                  · linarith only [h1406, h1557, hlam]
                                  · linarith only [h1467, h1557, hlam]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [h1489, h1492, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1531_1, u3ehi3]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [h1467, hlam, p1531_1]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [h1487, hlam, p1531_1]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [h1489, hlam, p1531_0]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [hlam, p1531_0]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [h1492, hlam, p1531_0]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [h1468, hlam, p1531_0]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [h1488, hlam, p1531_0]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [h1491, hlam, p1531_0]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [h1468, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1531_1, u3ehi3]
                                · obtain ⟨p1531_0, p1531_1, p1531_2, p1531_3⟩ := h1531c
                                  linarith only [hlam, p1531_0]
                            · linarith only [h1467, h1468, h1469, h1485, h1491, h935, hc12, hc23, hlam, hphi]
                          · linarith only [h1467, h1469, h1490, h935, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h0, h1467, h1469, h1489, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · linarith only [h1007, h1468, h1488, hlam]
                    · linarith only [h1467, h1487, h935, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1576 | h1576
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1577 | h1577
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1578 | h1578
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1579 | h1579
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1580 | h1580
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1581 | h1581
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1582 | h1582
                            · linarith only [h1467, h1468, h1576, h1580, h1582, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h1406, h1576, h1578, h1579, h1582, hc01, hc12, hlam, hphi]
                          · linarith only [h1076, h1467, h1581, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1076, h1467, h1580, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1587 | h1587
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1588 | h1588
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1589 | h1589
                            · linarith only [h1007, h1579, h1589, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1591 | h1591
                              · linarith only [h0, h1406, h1467, h1577, h1579, h1591, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · rcases h4bigk with h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [hlam, p1593_0]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h1007, hlam, p1593_1]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h1406, hlam, p1593_0]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h1406, h1577, h1579, hc45, hlam, hphi, p1593_1, u4ehi3]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h1468, hlam, p1593_0]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h1579, hc45, hlam, hphi, p1593_1, u4ehi0]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [hlam, p1593_0]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h1579, hc45, hlam, hphi, p1593_1, u4ehi2]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h1579, hc45, hlam, hphi, ht34, p1593_1, u3ehi3]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h1579, hlam, p1593_0]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h1467, h1577, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1593_1, u3ehi3]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h1577, hlam, p1593_1]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [hlam, p1593_0]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h1577, h1579, hc45, hlam, hphi, ht34, p1593_1, u3ehi3]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h1589, hlam, p1593_0]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h1467, hlam, p1593_1]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h1578, hlam, p1593_1]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h1587, hlam, p1593_0]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [hlam, p1593_0]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h1591, hlam, p1593_0]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h1467, hc45, hlam, hphi, ht34, p1593_1, u3ehi3]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [hc45, hlam, hphi, p1593_1, u4ehi1]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [h0, h1406, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1593_1]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [hc45, hlam, hphi, ht34, p1593_1, u3ehi3]
                                · obtain ⟨p1593_0, p1593_1, p1593_2, p1593_3⟩ := h1593c
                                  linarith only [hlam, p1593_0]
                          · linarith only [h1076, h1467, h1588, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1076, h1467, h1587, hlam]
                    · linarith only [h1076, h1467, h1578, h935, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h1076, h1467, h1576, h1577, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1623 | h1623
                  · linarith only [h0, h1406, h1576, h1623, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1625 | h1625
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1626 | h1626
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1627 | h1627
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1628 | h1628
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1629 | h1629
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1630 | h1630
                              · linarith only [h1467, h1468, h1630, hlam]
                              · rcases h4bigk with h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [hlam, p1632_0]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [h1007, hlam, p1632_1]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [h1406, hlam, p1632_0]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [h1468, h1625, h1626, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1632_1, u3ehi3]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [h1468, hlam, p1632_0]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  rcases p1632_3 (m.d 0 4) (by simp) with h1638 | h1638
                                  · linarith only [h1007, h1638, hlam]
                                  · rcases p1632_3 (m.d 1 4) (by simp) with h1640 | h1640
                                    · rcases p1632_3 (m.d 2 4) (by simp) with h1641 | h1641
                                      · rcases p1632_3 (m.d 3 4) (by simp) with h1642 | h1642
                                        · linarith only [h1625, h1642, hlam]
                                        · rcases p1632_3 (m.d 4 5) (by simp) with h1644 | h1644
                                          · linarith only [h1626, h1644, hlam]
                                          · linarith only [h1468, h1644, hlam]
                                      · linarith only [h1406, h1641, hlam]
                                    · linarith only [h1007, h1640, hlam]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [hlam, p1632_0]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [h1623, hlam, p1632_0]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  rcases p1632_3 (m.d 0 4) (by simp) with h1651 | h1651
                                  · linarith only [h1007, h1651, hlam]
                                  · linarith only [h1467, h1651, hlam]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [h1468, h1576, h1625, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1632_1, u4ehi0]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  rcases p1632_3 (m.d 0 4) (by simp) with h1655 | h1655
                                  · linarith only [h1406, h1655, hlam]
                                  · rcases p1632_3 (m.d 1 4) (by simp) with h1657 | h1657
                                    · linarith only [h1623, h1657, hlam]
                                    · linarith only [h1007, h1657, hlam]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [h1007, h1627, hc01, hc23, hlam, hphi, ht12, p1632_1]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [hlam, p1632_0]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  rcases p1632_3 (m.d 0 4) (by simp) with h1662 | h1662
                                  · linarith only [h1406, h1662, hlam]
                                  · linarith only [h1467, h1662, hlam]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [h1467, h1468, h1627, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1632_1, u3ehi3]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [h1467, hlam, p1632_1]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [h1625, hlam, p1632_1]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [h1627, hlam, p1632_0]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [hlam, p1632_0]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [h1630, hlam, p1632_0]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [h1467, h1626, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1632_1, u3ehi3]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [h1626, hlam, p1632_0]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [h1629, hlam, p1632_0]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [h1623, h1626, h1627, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1632_1, u3ehi3]
                                · obtain ⟨p1632_0, p1632_1, p1632_2, p1632_3⟩ := h1632c
                                  linarith only [hlam, p1632_0]
                            · linarith only [h1623, h1626, h1629, hlam]
                          · linarith only [h1467, h1576, h1628, h935, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1467, h1468, h1576, h1625, h1626, h1627, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1679 | h1679
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1680 | h1680
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1681 | h1681
                            · linarith only [h1007, h1626, h1679, h1681, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h1623, h1681, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h1076, h1467, h1680, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h0, h1467, h1576, h1679, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · linarith only [h1467, h1468, h1625, h935, hc45, hlam, hphi, ht34, u3ehi0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1687 | h1687
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1688 | h1688
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1689 | h1689
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1690 | h1690
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1691 | h1691
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1692 | h1692
                        · linarith only [h1467, h1688, h1692, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h0, h1076, h1690, h1692, hc01, hc13, hlam, hphi]
                      · linarith only [h1406, h1687, h1689, h1691, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1696 | h1696
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1697 | h1697
                        · linarith only [h1690, h1697, h935, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1699 | h1699
                          · linarith only [h1688, h1690, h1699, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1701 | h1701
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1702 | h1702
                              · rcases h4bigk with h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [hlam, p1703_0]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h1007, hlam, p1703_1]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h1406, hlam, p1703_0]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h1467, hlam, p1703_0]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h1406, h1689, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1703_1, u4ehi4]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h1687, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1703_1, u4ehi4]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [hlam, p1703_0]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h1406, h1687, h1689, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1703_1, u4ehi4]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h1690, hlam, p1703_0]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  rcases p1703_3 (m.d 0 4) (by simp) with h1713 | h1713
                                  · linarith only [h1007, h1713, hlam]
                                  · linarith only [h1687, h1713, hlam]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h1687, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1703_1, u4ehi4]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h1689, hlam, p1703_1]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [hlam, p1703_0]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h1697, hlam, p1703_1]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h1689, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1703_1, u4ehi4]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h1687, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1703_1, u4ehi4]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h1007, hc01, hc34, hlam, hphi, ht12, ht23, p1703_1]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h0, h1406, hc01, hc34, hlam, hphi, ht12, ht23, p1703_1]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [hlam, p1703_0]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  rcases p1703_3 (m.d 0 4) (by simp) with h1725 | h1725
                                  · linarith only [h1467, h1725, hlam]
                                  · linarith only [h1687, h1725, hlam]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h1687, hlam, p1703_0]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h1696, hlam, p1703_0]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h1701, hlam, p1703_0]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [h1702, hlam, p1703_0]
                                · obtain ⟨p1703_0, p1703_1, p1703_2, p1703_3⟩ := h1703c
                                  linarith only [hlam, p1703_0]
                              · linarith only [h1467, h1687, h1702, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h1406, h1687, h1701, hlam]
                      · linarith only [h1406, h1687, h1689, h1696, hlam]
                  · linarith only [h0, h1076, h1688, h1689, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1737 | h1737
                  · linarith only [h0, h1406, h1688, h1737, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1739 | h1739
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1740 | h1740
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1741 | h1741
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1742 | h1742
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1743 | h1743
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1744 | h1744
                              · rcases h4bigk with h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [hlam, p1745_0]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1007, hlam, p1745_1]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1406, hlam, p1745_0]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1467, hlam, p1745_0]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1467, h1739, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1745_1, u4ehi4]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1687, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1745_1, u4ehi4]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [hlam, p1745_0]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1737, hlam, p1745_0]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1467, h1737, h1741, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1745_1, u3ehi0]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  rcases p1745_3 (m.d 0 4) (by simp) with h1755 | h1755
                                  · linarith only [h1007, h1755, hlam]
                                  · linarith only [h1687, h1755, hlam]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1687, h1741, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1745_1, u4ehi4]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1007, h1741, hc01, hc23, hlam, hphi, ht12, p1745_1]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [hlam, p1745_0]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1467, h1741, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1745_1, u3ehi0]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  rcases p1745_3 (m.d 0 4) (by simp) with h1762 | h1762
                                  · linarith only [h1406, h1762, hlam]
                                  · linarith only [h1687, h1762, hlam]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1687, h1739, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1745_1, u4ehi4]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1739, hlam, p1745_1]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1741, hlam, p1745_0]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [hlam, p1745_0]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1688, h1739, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1745_1, u4ehi4]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1687, hlam, p1745_0]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1740, hlam, p1745_0]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1743, hlam, p1745_0]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [h1744, hlam, p1745_0]
                                · obtain ⟨p1745_0, p1745_1, p1745_2, p1745_3⟩ := h1745c
                                  linarith only [hlam, p1745_0]
                              · linarith only [h1467, h1687, h1744, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h1467, h1687, h1688, h1737, h1739, h1743, hc12, hc23, hlam, hphi]
                          · linarith only [h1467, h1688, h1739, h1742, hc35, hlam, hphi, u3ehi0]
                        · linarith only [h1688, h1739, h1741, hlam]
                      · linarith only [h1467, h1687, h1688, h1739, h1740, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1780 | h1780
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1781 | h1781
                        · linarith only [h0, h1688, h1739, h1781, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h1688, h1781, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h1007, h1687, h1780, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1785 | h1785
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1786 | h1786
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1787 | h1787
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1788 | h1788
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1789 | h1789
                        · linarith only [h1467, h1785, h1789, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h0, h1076, h1785, h1787, h1789, hc01, hc12, hlam, hphi]
                      · linarith only [h1467, h1787, h1788, hc45, hlam, hphi, ht34, u3ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1793 | h1793
                      · linarith only [h1467, h1687, h1787, h1793, hc34, hlam, hphi, u3ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1795 | h1795
                        · linarith only [h1785, h1787, h1793, h1795, hc45, hlam, hphi, u4ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1797 | h1797
                          · linarith only [h1785, h1787, h1793, h1797, hc45, hlam, hphi, ht34, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1799 | h1799
                            · linarith only [h0, h1076, h1785, h1787, h1793, h1799, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1801 | h1801
                              · linarith only [h0, h1076, h1785, h1787, h1793, h1801, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h1467, h1801, hc45, hlam, hphi, ht34, u3ehi0]
                  · linarith only [h0, h1076, h1785, h1786, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1805 | h1805
                  · linarith only [h0, h1406, h1785, h1805, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1807 | h1807
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1808 | h1808
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1809 | h1809
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1810 | h1810
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1811 | h1811
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1812 | h1812
                              · linarith only [h1467, h1687, h1812, hc34, hlam, hphi, u3ehi0]
                              · linarith only [h1467, h1808, h1812, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h1805, h1808, h1811, hlam]
                          · linarith only [h0, h1805, h1809, h1810, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h1467, h1687, h1785, h1807, h1808, h1809, hc34, hlam, hphi, u3ehi0]
                      · linarith only [h1467, h1807, h1808, hc45, hlam, hphi, ht34, u3ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1819 | h1819
                      · linarith only [h1467, h1687, h1807, h1819, hc34, hlam, hphi, u3ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1821 | h1821
                        · linarith only [h1807, h1821, h935, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h1785, h1821, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
