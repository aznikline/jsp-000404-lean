import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4588000 in
set_option maxHeartbeats 4588000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                    · linarith only [h0, h10, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                      · linarith only [h0, h10, h12, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h14 | h14
                        · linarith only [h0, h10, h14, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h0, h14, h4, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h17, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
                      · linarith only [h0, h17, h19, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h21 | h21
                        · linarith only [h1, h21, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h0, h21, h4, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h25 | h25
                · linarith only [h25, h7, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h27 | h27
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
                    · linarith only [h0, h28, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                      · linarith only [h0, h28, h30, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                        · linarith only [h1, h32, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
                          · linarith only [h1, h34, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h36 | h36
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                              · linarith only [h37, h4, h7, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
                                · linarith only [h25, h39, h4, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h41 | h41
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h42 | h42
                                    · rcases h0bigk with h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [hlam, p43_0]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h30, h34, h41, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1, u0elo0, u3ehi1]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1, u0elo0, u3ehi0]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h30, h34, h41, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1, u0elo0, u3ehi1]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h1, h25, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1, u0elo0, u3ehi1]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h0, hlam, p43_0]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [hlam, p43_0]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1, u0elo1, u3ehi1]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h0, h30, h34, h41, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1, u0elo0, u3ehi1]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h0, h1, h25, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1, u0elo0, u3ehi1]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h1, hlam, p43_1]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h4, hlam, p43_1]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [hlam, p43_0]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h7, hlam, p43_1]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h25, hlam, p43_1]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h2, hlam, p43_0]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h5, hlam, p43_0]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1, u0elo3, u3ehi1]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [hlam, p43_0]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h30, h34, h6, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1, u0elo3, u3ehi1]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h3, hlam, p43_0]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h6, hlam, p43_1]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1, u0elo4, u3ehi1]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [h27, hlam, p43_1]
                                      · have p43_0 := h43c.1
                                        have p43_1 := h43c.2.1
                                        have p43_2 := h43c.2.2.1
                                        have p43_3 := h43c.2.2.2
                                        linarith only [hlam, p43_0]
                                    · linarith only [h0, h41, h42, h5, h7, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · linarith only [h2, h36, h41, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h27, h32, h36, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
                    · linarith only [h0, h72, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h74 | h74
                      · linarith only [h0, h4, h72, h74, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                        · linarith only [h1, h4, h7, h72, h76, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
                          · linarith only [h25, h4, h72, h78, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h80 | h80
                            · linarith only [h2, h27, h80, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                              · linarith only [h4, h7, h82, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h84 | h84
                                · linarith only [h25, h4, h84, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h86 | h86
                                  · linarith only [h27, h4, h7, h72, h86, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h88 | h88
                                    · linarith only [h27, h4, h7, h72, h88, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h4, h7, h72, h88, hc12, hc45, hlam, hphi, ht23, ht34]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h91 | h91
              · rcases m.htr 0 3 5 (by decide) (by decide) with h92 | h92
                · linarith only [h4, h6, h92, hlam]
                · linarith only [h91, h92, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h95 | h95
                · linarith only [h91, h95, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h97 | h97
                  · linarith only [h5, h6, h97, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
                    · linarith only [h0, h99, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · linarith only [h4, h6, h99, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h102 | h102
            · rcases m.htr 0 3 4 (by decide) (by decide) with h103 | h103
              · linarith only [h103, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h105 | h105
                · linarith only [h103, h105, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h107 | h107
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
                    · linarith only [h0, h108, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · linarith only [h108, h4, h5, hc12, hc24, hlam, hphi]
                  · linarith only [h107, h4, h5, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h112 | h112
              · linarith only [h112, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h114 | h114
                · linarith only [h112, h114, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h116 | h116
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h117 | h117
                    · linarith only [h0, h117, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · linarith only [h117, h4, h5, hc12, hc24, hlam, hphi]
                  · linarith only [h116, h4, h5, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h121 | h121
          · rcases m.htr 0 2 5 (by decide) (by decide) with h122 | h122
            · rcases m.htr 0 3 4 (by decide) (by decide) with h123 | h123
              · rcases m.htr 0 3 5 (by decide) (by decide) with h124 | h124
                · rcases m.htr 0 4 5 (by decide) (by decide) with h125 | h125
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h126 | h126
                    · linarith only [h0, h126, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h128 | h128
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h129 | h129
                        · linarith only [h1, h129, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h123, h129, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h122, h128, h4, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h133 | h133
                    · linarith only [h0, h133, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h135 | h135
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h136 | h136
                        · linarith only [h1, h136, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h123, h125, h136, hc45, hlam, hphi, ht34, u3ehi1]
                      · linarith only [h122, h135, h4, hc12, hc23, hlam, hphi]
                · linarith only [h123, h124, hc35, hlam, hphi, u3ehi3]
              · linarith only [h121, h123, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h142 | h142
              · rcases m.htr 0 3 5 (by decide) (by decide) with h143 | h143
                · rcases m.htr 0 4 5 (by decide) (by decide) with h144 | h144
                  · linarith only [h121, h122, h144, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h146 | h146
                    · linarith only [h0, h146, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h148 | h148
                      · linarith only [h0, h121, h122, h142, h148, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h150 | h150
                        · linarith only [h1, h150, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h142, h150, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                · linarith only [h142, h143, hc35, hlam, hphi, u3ehi3]
              · linarith only [h121, h142, h4, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h155 | h155
            · rcases m.htr 0 3 4 (by decide) (by decide) with h156 | h156
              · rcases m.htr 0 3 5 (by decide) (by decide) with h157 | h157
                · rcases m.htr 0 4 5 (by decide) (by decide) with h158 | h158
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h159 | h159
                    · linarith only [h0, h159, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h161 | h161
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h162 | h162
                        · linarith only [h1, h162, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h156, h162, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h121, h155, h161, hc12, hc24, hlam, hphi]
                  · linarith only [h121, h155, h158, hlam]
                · linarith only [h156, h157, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h168 | h168
                · linarith only [h156, h168, hc34, hlam, hphi, u3ehi4]
                · linarith only [h155, h168, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h171 | h171
              · rcases m.htr 0 3 5 (by decide) (by decide) with h172 | h172
                · rcases m.htr 0 4 5 (by decide) (by decide) with h173 | h173
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h174 | h174
                    · linarith only [h0, h174, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h176 | h176
                      · linarith only [h0, h155, h176, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h178 | h178
                        · linarith only [h1, h178, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h171, h178, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h181 | h181
                    · linarith only [h0, h181, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h183 | h183
                      · linarith only [h0, h155, h183, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h185 | h185
                        · linarith only [h1, h185, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h171, h185, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                · linarith only [h171, h172, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h189 | h189
                · linarith only [h171, h189, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h191 | h191
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h192 | h192
                    · linarith only [h0, h192, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h194 | h194
                      · linarith only [h0, h155, h194, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h196 | h196
                        · linarith only [h1, h171, h196, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h198 | h198
                          · linarith only [h1, h189, h198, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h200 | h200
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h201 | h201
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h202 | h202
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h203 | h203
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h204 | h204
                                    · rcases h0bigk with h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [hlam, p205_0]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        rcases p205_3 (m.d 0 1) (by simp) with h207 | h207
                                        · rcases p205_3 (m.d 0 2) (by simp) with h208 | h208
                                          · linarith only [h0, h208, hlam]
                                          · rcases p205_3 (m.d 0 3) (by simp) with h210 | h210
                                            · linarith only [h1, h210, hlam]
                                            · linarith only [h210, h4, hlam]
                                        · linarith only [h0, h207, hlam]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, p205_1, u0elo0, u3ehi1]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h1, h189, h191, hlam, hphi, ht0b, ht34, ht45, ht5b, p205_1, u0elo0, u3ehi1]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h1, h189, hlam, hphi, ht0b, ht34, ht45, ht5b, p205_1, u0elo0, u3ehi1]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h0, hlam, p205_0]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [hlam, p205_0]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h4, hlam, p205_0]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h121, hlam, p205_1]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h155, hlam, p205_0]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h1, hlam, p205_1]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h189, h201, h204, hc02, hc23, hlam, hphi, p205_1]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [hlam, p205_0]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h171, hlam, p205_1]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h189, hlam, p205_1]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h2, hlam, p205_0]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h0, h171, h201, hc12, hc23, hlam, hphi, p205_1]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h1, h171, h201, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p205_1, u3ehi1]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [hlam, p205_0]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h1, h171, h189, h201, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p205_1, u3ehi1]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h3, hlam, p205_0]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h0, h171, h191, h201, hc12, hc23, hlam, hphi, p205_1]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h1, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, p205_1, u0elo0, u3ehi1]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [h191, hlam, p205_1]
                                      · have p205_0 := h205c.1
                                        have p205_1 := h205c.2.1
                                        have p205_2 := h205c.2.2.1
                                        have p205_3 := h205c.2.2.2
                                        linarith only [hlam, p205_0]
                                    · linarith only [h1, h171, h204, hc45, hlam, hphi, ht34, u3ehi1]
                                  · linarith only [h2, h200, h203, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h1, h171, h201, h202, hc35, hlam, hphi, u3ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h240 | h240
                                · linarith only [h201, h240, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h242 | h242
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h243 | h243
                                    · rcases h0bigk with h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [hlam, p244_0]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        rcases p244_3 (m.d 0 1) (by simp) with h246 | h246
                                        · rcases p244_3 (m.d 0 2) (by simp) with h247 | h247
                                          · linarith only [h0, h247, hlam]
                                          · rcases p244_3 (m.d 0 3) (by simp) with h249 | h249
                                            · linarith only [h1, h249, hlam]
                                            · linarith only [h249, h4, hlam]
                                        · linarith only [h0, h246, hlam]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p244_1, u0elo0, u3ehi0]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [h198, h2, h200, hlam, hphi, ht0b, ht34, ht45, ht5b, p244_1, u0elo0, u3ehi1]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [h198, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, p244_1, u0elo0, u3ehi1]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [h0, hlam, p244_0]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [hlam, p244_0]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [h4, hlam, p244_0]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [h121, hlam, p244_1]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [h155, hlam, p244_0]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [h1, hlam, p244_1]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [h0, h240, h243, h4, hc12, hc34, hlam, hphi, ht23, p244_1]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [hlam, p244_0]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [h171, hlam, p244_1]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [h189, hlam, p244_1]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [h2, hlam, p244_0]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        rcases p244_3 (m.d 0 1) (by simp) with h267 | h267
                                        · rcases p244_3 (m.d 0 2) (by simp) with h268 | h268
                                          · linarith only [h121, h268, hlam]
                                          · rcases p244_3 (m.d 0 3) (by simp) with h270 | h270
                                            · linarith only [h171, h270, hlam]
                                            · linarith only [h270, h4, hlam]
                                        · linarith only [h0, h267, hlam]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p244_1, u0elo3, u3ehi0]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [hlam, p244_0]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [h198, h2, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, p244_1, u0elo0, u3ehi1]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [h3, hlam, p244_0]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        rcases p244_3 (m.d 0 1) (by simp) with h278 | h278
                                        · rcases p244_3 (m.d 0 2) (by simp) with h279 | h279
                                          · linarith only [h155, h279, hlam]
                                          · rcases p244_3 (m.d 0 3) (by simp) with h281 | h281
                                            · linarith only [h189, h281, hlam]
                                            · linarith only [h281, h4, hlam]
                                        · linarith only [h0, h278, hlam]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, p244_1, u0elo4, u3ehi1]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [h191, hlam, p244_1]
                                      · have p244_0 := h244c.1
                                        have p244_1 := h244c.2.1
                                        have p244_2 := h244c.2.2.1
                                        have p244_3 := h244c.2.2.2
                                        linarith only [hlam, p244_0]
                                    · linarith only [h2, h200, h243, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · linarith only [h121, h2, h200, h242, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h191, h196, h200, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h291 | h291
                    · linarith only [h0, h291, h4, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h293 | h293
                      · linarith only [h0, h155, h293, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h295 | h295
                        · linarith only [h1, h171, h295, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h297 | h297
                          · linarith only [h1, h189, h297, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h299 | h299
                            · linarith only [h191, h2, h299, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h301 | h301
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h302 | h302
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h303 | h303
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h304 | h304
                                    · linarith only [h1, h171, h191, h304, hc34, hlam, hphi, u3ehi1]
                                    · linarith only [h1, h171, h301, h303, h304, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                                  · linarith only [h1, h171, h301, h303, hc45, hlam, hphi, ht34, u3ehi1]
                                · linarith only [h1, h171, h301, h302, hc35, hlam, hphi, u3ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h309 | h309
                                · linarith only [h301, h309, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h311 | h311
                                  · linarith only [h1, h171, h191, h301, h311, hc34, hlam, hphi, u3ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h313 | h313
                                    · linarith only [h301, h311, h313, hc34, hlam, hphi, u3ehi2]
                                    · linarith only [h1, h171, h313, hc45, hlam, hphi, ht34, u3ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h316 | h316
        · rcases m.htr 0 2 4 (by decide) (by decide) with h317 | h317
          · rcases m.htr 0 2 5 (by decide) (by decide) with h318 | h318
            · linarith only [h0, h3, h318, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h320 | h320
              · rcases m.htr 0 3 5 (by decide) (by decide) with h321 | h321
                · linarith only [h0, h3, h316, h321, hlam]
                · linarith only [h320, h321, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h324 | h324
                · linarith only [h320, h324, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h326 | h326
                  · linarith only [h0, h3, h317, h326, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h328 | h328
                    · linarith only [h0, h328, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · linarith only [h316, h318, h328, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h331 | h331
            · linarith only [h0, h3, h331, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h333 | h333
              · linarith only [h316, h317, h333, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h335 | h335
                · linarith only [h333, h335, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h337 | h337
                  · linarith only [h2, h3, h337, hlam]
                  · linarith only [h316, h317, h337, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h340 | h340
          · rcases m.htr 0 2 5 (by decide) (by decide) with h341 | h341
            · linarith only [h0, h3, h341, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h343 | h343
              · rcases m.htr 0 3 5 (by decide) (by decide) with h344 | h344
                · linarith only [h1, h3, h344, hlam]
                · linarith only [h343, h344, hc35, hlam, hphi, u3ehi3]
              · linarith only [h316, h340, h343, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h348 | h348
            · linarith only [h1, h3, h316, h348, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h350 | h350
              · rcases m.htr 0 3 5 (by decide) (by decide) with h351 | h351
                · linarith only [h1, h3, h351, hlam]
                · linarith only [h350, h351, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h354 | h354
                · linarith only [h350, h354, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h356 | h356
                  · linarith only [h2, h3, h356, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h358 | h358
                    · linarith only [h0, h316, h358, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h360 | h360
                      · linarith only [h0, h3, h348, h360, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h362 | h362
                        · linarith only [h1, h350, h362, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h364 | h364
                          · linarith only [h1, h350, h364, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h2, h3, h362, h364, hc35, hlam, hphi, u3ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h367 | h367
      · rcases m.htr 0 2 3 (by decide) (by decide) with h368 | h368
        · rcases m.htr 0 2 4 (by decide) (by decide) with h369 | h369
          · linarith only [h0, h2, h369, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h371 | h371
            · rcases m.htr 0 3 4 (by decide) (by decide) with h372 | h372
              · linarith only [h0, h2, h368, h372, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h374 | h374
                · linarith only [h372, h374, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h376 | h376
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h377 | h377
                    · linarith only [h0, h2, h377, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                    · linarith only [h368, h369, h377, hc12, hc24, hlam, hphi]
                  · linarith only [h1, h2, h376, hc45, hlam, hphi, ht34, u3ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h381 | h381
              · linarith only [h2, h367, h368, h371, h381, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h383 | h383
                · linarith only [h381, h383, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h385 | h385
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h386 | h386
                    · linarith only [h0, h2, h386, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                    · linarith only [h368, h369, h386, hc12, hc24, hlam, hphi]
                  · linarith only [h2, h367, h368, h371, h385, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h390 | h390
          · linarith only [h0, h2, h390, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h392 | h392
            · rcases m.htr 0 3 4 (by decide) (by decide) with h393 | h393
              · linarith only [h1, h2, h393, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h395 | h395
                · linarith only [h393, h395, hc34, hlam, hphi, u3ehi4]
                · linarith only [h368, h392, h395, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h398 | h398
              · linarith only [h1, h2, h398, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h400 | h400
                · linarith only [h398, h400, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h402 | h402
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h403 | h403
                    · linarith only [h0, h403, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h405 | h405
                      · linarith only [h0, h2, h392, h405, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h407 | h407
                        · linarith only [h1, h2, h407, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                        · linarith only [h1, h2, h407, hc34, hlam, hphi, u3ehi1]
                  · linarith only [h1, h2, h402, hc45, hlam, hphi, ht34, u3ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h411 | h411
        · rcases m.htr 0 2 4 (by decide) (by decide) with h412 | h412
          · linarith only [h0, h2, h412, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h414 | h414
            · linarith only [h0, h367, h414, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h416 | h416
              · linarith only [h0, h2, h411, h416, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h418 | h418
                · linarith only [h416, h418, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h420 | h420
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h421 | h421
                    · linarith only [h0, h367, h420, h421, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                    · linarith only [h411, h412, h421, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h2, h411, h420, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h425 | h425
          · linarith only [h1, h2, h411, h425, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h427 | h427
            · linarith only [h1, h367, h411, h427, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h429 | h429
              · linarith only [h1, h2, h429, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h431 | h431
                · linarith only [h429, h431, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h433 | h433
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h434 | h434
                    · linarith only [h0, h411, h434, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h436 | h436
                      · linarith only [h0, h367, h427, h436, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h438 | h438
                        · linarith only [h1, h367, h436, h438, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1, h2, h438, hc34, hlam, hphi, u3ehi1]
                  · linarith only [h1, h2, h433, hc45, hlam, hphi, ht34, u3ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h442 | h442
    · rcases m.htr 0 1 5 (by decide) (by decide) with h443 | h443
      · rcases m.htr 0 2 3 (by decide) (by decide) with h444 | h444
        · linarith only [h0, h1, h444, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h446 | h446
          · rcases m.htr 0 2 5 (by decide) (by decide) with h447 | h447
            · rcases m.htr 0 3 4 (by decide) (by decide) with h448 | h448
              · rcases m.htr 0 3 5 (by decide) (by decide) with h449 | h449
                · rcases m.htr 0 4 5 (by decide) (by decide) with h450 | h450
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h451 | h451
                    · linarith only [h0, h444, h446, h451, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h453 | h453
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h454 | h454
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h455 | h455
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h456 | h456
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h457 | h457
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h458 | h458
                                · linarith only [h0, h453, h458, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                                · linarith only [h0, h1, h451, h453, h455, h456, h458, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h1, h442, h451, h454, h457, hlam]
                            · linarith only [h0, h446, h450, h454, h456, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h0, h1, h455, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h453, h454, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h444, h447, h453, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h466 | h466
                    · linarith only [h0, h1, h444, h466, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h468 | h468
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h469 | h469
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h470 | h470
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h471 | h471
                            · linarith only [h442, h450, h471, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h473 | h473
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h474 | h474
                                · linarith only [h0, h1, h466, h468, h474, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                                · linarith only [h0, h1, h466, h474, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h466, h468, h469, h471, h473, hlam]
                          · linarith only [h0, h1, h470, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h469, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h1, h447, h466, h468, hc12, hc23, hlam, hphi]
                · linarith only [h448, h449, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h442, h448, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h483 | h483
              · rcases m.htr 0 3 5 (by decide) (by decide) with h484 | h484
                · rcases m.htr 0 4 5 (by decide) (by decide) with h485 | h485
                  · linarith only [h446, h447, h485, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h487 | h487
                    · linarith only [h0, h487, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h489 | h489
                      · linarith only [h0, h1, h447, h487, h489, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h491 | h491
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h492 | h492
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h493 | h493
                            · linarith only [h442, h485, h493, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h495 | h495
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h496 | h496
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h497 | h497
                                  · linarith only [h446, h447, h485, h497, hlam]
                                  · linarith only [h446, h447, h495, h497, hc45, hlam, hphi, ht34, u3ehi3]
                                · linarith only [h1, h443, h446, h447, h487, h492, h495, h496, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h1, h442, h443, h487, h489, h491, h495, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h1, h442, h491, h492, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h0, h1, h491, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h483, h484, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h443, h446, h447, h483, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h506 | h506
            · rcases m.htr 0 3 4 (by decide) (by decide) with h507 | h507
              · rcases m.htr 0 3 5 (by decide) (by decide) with h508 | h508
                · rcases m.htr 0 4 5 (by decide) (by decide) with h509 | h509
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h510 | h510
                    · linarith only [h0, h1, h444, h506, h510, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h512 | h512
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h513 | h513
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h514 | h514
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h515 | h515
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h516 | h516
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h517 | h517
                                · linarith only [h0, h1, h510, h512, h517, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                                · linarith only [h0, h1, h443, h510, h514, h517, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                              · linarith only [h0, h1, h510, h512, h514, h516, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h509, h513, h515, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                          · linarith only [h0, h1, h514, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h507, h512, h513, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h446, h506, h512, hc12, hc24, hlam, hphi]
                  · linarith only [h446, h506, h509, hlam]
                · linarith only [h507, h508, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h442, h507, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h528 | h528
              · rcases m.htr 0 3 5 (by decide) (by decide) with h529 | h529
                · rcases m.htr 0 4 5 (by decide) (by decide) with h530 | h530
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h531 | h531
                    · linarith only [h0, h531, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h533 | h533
                      · linarith only [h0, h1, h506, h531, h533, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h535 | h535
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h536 | h536
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h537 | h537
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h538 | h538
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h539 | h539
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h540 | h540
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h541 | h541
                                    · rcases h0bigk with h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [hlam, p542_0]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h0, h1, h531, hc12, hc23, hlam, hphi, p542_1]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h1, hlam, p542_0]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h0, h1, h446, h531, hc12, hc23, hlam, hphi, p542_1]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h0, h1, h506, h531, hc12, hc23, hlam, hphi, p542_1]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h0, hlam, p542_0]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [hlam, p542_0]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h444, hlam, p542_0]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h446, hlam, p542_1]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h506, hlam, p542_0]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p542_1, u0elo2]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        rcases p542_3 (m.d 0 1) (by simp) with h554 | h554
                                        · linarith only [h1, h554, hlam]
                                        · linarith only [h0, h554, hlam]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [hlam, p542_0]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h442, h535, h541, hlam, hphi, ht0b, ht34, ht45, ht5b, p542_1, u0elo2, u3ehi4]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h443, h536, hlam, hphi, ht0b, ht34, ht45, ht5b, p542_1, u0elo2, u3ehi4]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h442, hlam, p542_0]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h0, h1, h442, h531, hc12, hc23, hlam, hphi, p542_1]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h528, hlam, p542_0]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [hlam, p542_0]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h1, h442, h443, h531, h536, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p542_1, u3ehi4]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h443, hlam, p542_0]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h0, h1, h443, h531, hc12, hc23, hlam, hphi, p542_1]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h529, hlam, p542_0]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [h530, hlam, p542_1]
                                      · have p542_0 := h542c.1
                                        have p542_1 := h542c.2.1
                                        have p542_2 := h542c.2.2.1
                                        have p542_3 := h542c.2.2.2
                                        linarith only [hlam, p542_0]
                                    · linarith only [h1, h442, h530, h531, h541, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h1, h442, h531, h537, h540, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h1, h442, h531, h537, h539, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h442, h531, h535, h538, hlam]
                            · linarith only [h442, h530, h535, h537, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h0, h1, h536, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h442, h528, h535, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h577 | h577
                    · linarith only [h0, h577, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h579 | h579
                      · linarith only [h0, h506, h579, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h581 | h581
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h582 | h582
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h583 | h583
                            · linarith only [h1, h442, h530, h577, h583, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h585 | h585
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h586 | h586
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h587 | h587
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h588 | h588
                                    · linarith only [h1, h442, h446, h530, h577, h581, h588, hc02, hc23, hlam, hphi]
                                    · rcases h0bigk with h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [hlam, p590_0]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h0, h1, h577, hc12, hc23, hlam, hphi, p590_1]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h1, hlam, p590_0]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h1, h442, h577, h581, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p590_1, u3ehi3]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h1, h443, h577, h582, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p590_1, u3ehi4]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h0, hlam, p590_0]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [hlam, p590_0]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h444, hlam, p590_0]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h446, hlam, p590_1]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h506, hlam, p590_0]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p590_1, u0elo2]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        rcases p590_3 (m.d 0 1) (by simp) with h602 | h602
                                        · linarith only [h1, h602, hlam]
                                        · linarith only [h0, h602, hlam]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [hlam, p590_0]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h442, h581, hlam, hphi, ht0b, ht34, ht45, ht5b, p590_1, u0elo2, u3ehi3]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h442, h530, h581, hlam, hphi, ht0b, ht34, ht45, ht5b, p590_1, u0elo2, u3ehi3]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h442, hlam, p590_0]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h0, h530, h587, hc12, hc24, hlam, hphi, p590_1]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h528, hlam, p590_0]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [hlam, p590_0]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h530, hlam, p590_0]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h443, hlam, p590_0]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h0, h1, h443, h577, hc12, hc23, hlam, hphi, p590_1]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h529, hlam, p590_0]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [h1, h442, h443, h577, h581, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p590_1, u3ehi3]
                                      · have p590_0 := h590c.1
                                        have p590_1 := h590c.2.1
                                        have p590_2 := h590c.2.2.1
                                        have p590_3 := h590c.2.2.2
                                        linarith only [hlam, p590_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h618 | h618
                                    · linarith only [h1, h442, h577, h581, h587, h618, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases h0bigk with h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h0, h1, h577, hc12, hc23, hlam, hphi, p620_1]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h1, hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h1, h442, h577, h581, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p620_1, u3ehi3]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h0, h1, h506, h577, hc12, hc23, hlam, hphi, p620_1]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h0, hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h444, hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h446, hlam, p620_1]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h506, hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p620_1, u0elo2]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        rcases p620_3 (m.d 0 1) (by simp) with h632 | h632
                                        · linarith only [h1, h632, hlam]
                                        · linarith only [h0, h632, hlam]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h442, h581, hlam, hphi, ht0b, ht34, ht45, ht5b, p620_1, u0elo2, u3ehi3]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h442, h530, h581, hlam, hphi, ht0b, ht34, ht45, ht5b, p620_1, u0elo2, u3ehi3]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h442, hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h0, h1, h442, h577, hc12, hc23, hlam, hphi, p620_1]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h528, hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h530, hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h443, hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h0, h1, h443, h577, hc12, hc23, hlam, hphi, p620_1]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h529, hlam, p620_0]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [h1, h442, h443, h577, h581, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p620_1, u3ehi3]
                                      · have p620_0 := h620c.1
                                        have p620_1 := h620c.2.1
                                        have p620_2 := h620c.2.2.1
                                        have p620_3 := h620c.2.2.2
                                        linarith only [hlam, p620_0]
                                · linarith only [h1, h443, h577, h582, h586, hlam]
                              · linarith only [h1, h442, h443, h577, h581, h585, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h1, h442, h581, h582, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h0, h1, h581, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h528, h529, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h442, h528, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h654 | h654
        · linarith only [h0, h1, h654, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h656 | h656
          · rcases m.htr 0 2 5 (by decide) (by decide) with h657 | h657
            · linarith only [h0, h443, h657, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h659 | h659
              · rcases m.htr 0 3 5 (by decide) (by decide) with h660 | h660
                · rcases m.htr 0 4 5 (by decide) (by decide) with h661 | h661
                  · linarith only [h0, h443, h656, h661, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h663 | h663
                    · linarith only [h0, h654, h656, h663, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h665 | h665
                      · linarith only [h0, h443, h657, h665, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h667 | h667
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h668 | h668
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h669 | h669
                            · linarith only [h442, h661, h669, hlam]
                            · linarith only [h442, h443, h667, h669, hc45, hlam, hphi, ht34, u3ehi3]
                          · linarith only [h1, h442, h667, h668, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h0, h1, h667, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h659, h660, hc35, hlam, hphi, u3ehi3]
              · linarith only [h0, h1, h656, h659, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h676 | h676
            · linarith only [h0, h443, h676, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h678 | h678
              · rcases m.htr 0 3 5 (by decide) (by decide) with h679 | h679
                · rcases m.htr 0 4 5 (by decide) (by decide) with h680 | h680
                  · linarith only [h442, h443, h680, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h682 | h682
                    · linarith only [h0, h682, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h684 | h684
                      · linarith only [h0, h676, h684, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h686 | h686
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h687 | h687
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h688 | h688
                            · linarith only [h442, h443, h680, h682, h687, h688, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h442, h443, h686, h688, hc45, hlam, hphi, ht34, u3ehi3]
                          · linarith only [h679, h687, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                        · linarith only [h1, h442, h678, h686, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · linarith only [h678, h679, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h442, h678, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h695 | h695
      · rcases m.htr 0 2 3 (by decide) (by decide) with h696 | h696
        · linarith only [h0, h1, h696, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h698 | h698
          · linarith only [h0, h442, h698, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h700 | h700
            · rcases m.htr 0 3 4 (by decide) (by decide) with h701 | h701
              · rcases m.htr 0 3 5 (by decide) (by decide) with h702 | h702
                · rcases m.htr 0 4 5 (by decide) (by decide) with h703 | h703
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h704 | h704
                    · linarith only [h0, h696, h704, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h706 | h706
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h707 | h707
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h708 | h708
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h709 | h709
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h710 | h710
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h711 | h711
                                · linarith only [h0, h442, h704, h706, h707, h711, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                                · linarith only [h0, h442, h695, h704, h707, h708, h711, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                              · linarith only [h0, h442, h701, h704, h706, h707, h708, h710, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi4]
                            · linarith only [h0, h442, h706, h708, h709, hc45, hlam, hphi, ht34, u3ehi4]
                          · linarith only [h0, h442, h707, h708, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h701, h706, h707, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h0, h1, h700, h704, h706, hc12, hc23, hlam, hphi]
                  · linarith only [h442, h695, h703, hlam]
                · linarith only [h701, h702, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h721 | h721
                · linarith only [h701, h721, hc34, hlam, hphi, u3ehi4]
                · linarith only [h0, h1, h700, h721, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h724 | h724
              · rcases m.htr 0 3 5 (by decide) (by decide) with h725 | h725
                · rcases m.htr 0 4 5 (by decide) (by decide) with h726 | h726
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h727 | h727
                    · linarith only [h0, h727, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h729 | h729
                      · linarith only [h0, h700, h729, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h731 | h731
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h732 | h732
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h733 | h733
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h734 | h734
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h735 | h735
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h736 | h736
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h737 | h737
                                    · rcases h0bigk with h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h0, h442, h727, h731, hc12, hc23, hlam, hphi, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h1, hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h442, hlam, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h442, h695, h727, h731, h732, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p738_1, u3ehi4]
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
                                        linarith only [h696, hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h698, hlam, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h700, hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p738_1, u0elo2]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        rcases p738_3 (m.d 0 1) (by simp) with h750 | h750
                                        · linarith only [h1, h750, hlam]
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
                                        linarith only [h442, h695, h732, hlam, hphi, ht0b, ht34, ht45, ht5b, p738_1, u0elo2, u3ehi4]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h695, h732, hlam, hphi, ht0b, ht34, ht45, ht5b, p738_1, u0elo2, u3ehi4]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h695, h732, hlam, hphi, ht0b, ht34, ht45, ht5b, p738_1, u0elo3, u3ehi4]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        rcases p738_3 (m.d 0 1) (by simp) with h757 | h757
                                        · linarith only [h442, h757, hlam]
                                        · linarith only [h0, h757, hlam]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h724, hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h695, h724, h732, hlam, hphi, ht0b, ht34, ht45, ht5b, p738_1, u0elo2, u3ehi4]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h695, hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h0, h442, h695, h727, h731, hc12, hc23, hlam, hphi, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h725, hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h726, hlam, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [hlam, p738_0]
                                    · linarith only [h724, h726, h737, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                                  · linarith only [h442, h695, h698, h733, h736, hlam]
                                · linarith only [h442, h695, h727, h731, h732, h735, hlam]
                              · linarith only [h442, h695, h727, h731, h732, h734, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h442, h695, h732, h733, hc45, hlam, hphi, ht34, u3ehi4]
                          · linarith only [h0, h442, h731, h732, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h695, h724, h725, h731, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
                  · linarith only [h442, h695, h726, hlam]
                · linarith only [h724, h725, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h777 | h777
                · linarith only [h724, h777, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1, h695, h777, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h780 | h780
        · linarith only [h0, h1, h780, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h782 | h782
          · linarith only [h0, h442, h782, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h784 | h784
            · linarith only [h0, h695, h784, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h786 | h786
              · rcases m.htr 0 3 5 (by decide) (by decide) with h787 | h787
                · rcases m.htr 0 4 5 (by decide) (by decide) with h788 | h788
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h789 | h789
                    · linarith only [h0, h780, h789, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h791 | h791
                      · linarith only [h0, h695, h784, h791, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h793 | h793
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h794 | h794
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h795 | h795
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h796 | h796
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h797 | h797
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h798 | h798
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h799 | h799
                                    · rcases h0bigk with h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h695, h791, hc02, hc25, hlam, hphi, p800_1]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h1, hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h442, hlam, p800_1]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h695, hlam, p800_1]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h0, hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h780, hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h782, hlam, p800_1]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h784, hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1, u0elo2]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        rcases p800_3 (m.d 0 1) (by simp) with h812 | h812
                                        · linarith only [h1, h812, hlam]
                                        · linarith only [h0, h812, hlam]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h0, h442, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1, u0elo2]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h0, h695, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1, u0elo2]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1, u0elo3]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        rcases p800_3 (m.d 0 1) (by simp) with h819 | h819
                                        · linarith only [h442, h819, hlam]
                                        · linarith only [h0, h819, hlam]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h786, hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h0, h695, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1, u0elo3]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1, u0elo4]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        rcases p800_3 (m.d 0 1) (by simp) with h826 | h826
                                        · linarith only [h695, h826, hlam]
                                        · linarith only [h0, h826, hlam]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h787, hlam, p800_0]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [h788, hlam, p800_1]
                                      · have p800_0 := h800c.1
                                        have p800_1 := h800c.2.1
                                        have p800_2 := h800c.2.2.1
                                        have p800_3 := h800c.2.2.2
                                        linarith only [hlam, p800_0]
                                    · linarith only [h786, h788, h799, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                                  · linarith only [h0, h782, h786, h788, h798, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h780, h786, h797, hc35, hlam, hphi, u3ehi3]
                              · linarith only [h1, h787, h789, h796, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h0, h442, h786, h788, h795, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1, h786, h794, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1, h786, h793, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h839 | h839
                    · linarith only [h0, h839, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h841 | h841
                      · linarith only [h0, h442, h784, h788, h841, hc02, hc45, hlam, hphi, ht23, ht34]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h843 | h843
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h844 | h844
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h845 | h845
                            · linarith only [h0, h442, h788, h839, h843, h845, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h442, h845, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h787, h844, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                        · linarith only [h0, h1, h843, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h786, h787, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h851 | h851
                · linarith only [h786, h851, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h853 | h853
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h854 | h854
                    · linarith only [h0, h854, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h856 | h856
                      · linarith only [h0, h784, h856, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h858 | h858
                        · linarith only [h0, h1, h786, h854, h858, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h858, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h861 | h861
                    · linarith only [h0, h861, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h863 | h863
                      · linarith only [h0, h784, h863, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h865 | h865
                        · linarith only [h0, h1, h786, h861, h865, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h865, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 4588000 in
set_option maxHeartbeats 4588000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h868 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h869 | h869
  · rcases m.htr 0 1 5 (by decide) (by decide) with h870 | h870
    · rcases m.htr 0 2 3 (by decide) (by decide) with h871 | h871
      · rcases m.htr 0 2 4 (by decide) (by decide) with h872 | h872
        · rcases m.htr 0 2 5 (by decide) (by decide) with h873 | h873
          · rcases m.htr 0 3 4 (by decide) (by decide) with h874 | h874
            · rcases m.htr 0 3 5 (by decide) (by decide) with h875 | h875
              · rcases m.htr 0 4 5 (by decide) (by decide) with h876 | h876
                · rcases m.htr 1 2 3 (by decide) (by decide) with h877 | h877
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h878 | h878
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h879 | h879
                      · linarith only [h868, h879, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · linarith only [h874, h879, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                    · linarith only [h0, h868, h874, h878, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h868, h874, h877, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h884 | h884
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h885 | h885
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h886 | h886
                      · linarith only [h868, h886, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · linarith only [h874, h886, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                    · linarith only [h0, h868, h874, h885, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h868, h874, h884, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h874, h875, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h892 | h892
              · linarith only [h874, h892, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h894 | h894
                · rcases m.htr 1 2 3 (by decide) (by decide) with h895 | h895
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h896 | h896
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h897 | h897
                      · linarith only [h868, h874, h897, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h899 | h899
                        · linarith only [h868, h892, h899, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h901 | h901
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h902 | h902
                            · linarith only [h868, h874, h895, h902, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h904 | h904
                              · linarith only [h868, h892, h895, h904, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h906 | h906
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h907 | h907
                                  · rcases h0bigk with h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [hlam, p908_0]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h0, hlam, p908_1]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h0, h868, h895, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p908_1, u3ehi2]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h0, h868, h892, h894, h895, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p908_1, u3ehi2]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h0, h868, h892, h895, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p908_1, u3ehi2]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h868, h895, hlam, hphi, ht0b, ht34, ht45, ht5b, p908_1, u0elo1, u3ehi2]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [hlam, p908_0]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h868, h895, hlam, hphi, ht0b, ht34, ht45, ht5b, p908_1, u0elo1, u3ehi2]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h868, h892, h894, h895, hlam, hphi, ht0b, ht34, ht45, ht5b, p908_1, u0elo1, u3ehi2]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h868, h892, h895, hlam, hphi, ht0b, ht34, ht45, ht5b, p908_1, u0elo1, u3ehi2]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h868, hlam, p908_1]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h871, hlam, p908_1]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [hlam, p908_0]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h874, hlam, p908_1]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h892, hlam, p908_1]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h869, hlam, p908_0]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h872, hlam, p908_0]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h868, h895, hlam, hphi, ht0b, ht34, ht45, ht5b, p908_1, u0elo3, u3ehi2]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [hlam, p908_0]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h868, h892, h895, hlam, hphi, ht0b, ht34, ht45, ht5b, p908_1, u0elo3, u3ehi2]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h870, hlam, p908_0]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h873, hlam, p908_1]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h868, h895, hlam, hphi, ht0b, ht34, ht45, ht5b, p908_1, u0elo4, u3ehi2]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h894, hlam, p908_1]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [hlam, p908_0]
                                  · linarith only [h0, h869, h874, h901, h907, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h869, h901, h906, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h869, h894, h895, h897, h901, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h868, h895, h896, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h868, h895, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h939 | h939
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h940 | h940
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h941 | h941
                      · linarith only [h868, h874, h941, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h943 | h943
                        · linarith only [h868, h892, h943, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h945 | h945
                          · linarith only [h0, h869, h894, h945, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h947 | h947
                            · linarith only [h868, h874, h939, h947, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h949 | h949
                              · linarith only [h868, h892, h939, h949, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h951 | h951
                                · linarith only [h868, h872, h874, h894, h939, h951, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h953 | h953
                                  · linarith only [h868, h874, h894, h939, h953, hc34, hlam, hphi, u3ehi2]
                                  · linarith only [h868, h874, h939, h953, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h0, h868, h939, h940, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h868, h939, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h870, h873, hlam]
        · linarith only [h0, h869, h872, hlam]
      · linarith only [h0, h868, h871, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h961 | h961
      · rcases m.htr 0 2 4 (by decide) (by decide) with h962 | h962
        · rcases m.htr 0 2 5 (by decide) (by decide) with h963 | h963
          · rcases m.htr 0 3 4 (by decide) (by decide) with h964 | h964
            · rcases m.htr 0 3 5 (by decide) (by decide) with h965 | h965
              · linarith only [h868, h870, h965, hlam]
              · linarith only [h964, h965, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h968 | h968
              · linarith only [h964, h968, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h970 | h970
                · linarith only [h869, h870, h970, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h972 | h972
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h973 | h973
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h974 | h974
                      · linarith only [h868, h974, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h976 | h976
                        · linarith only [h869, h870, h963, h968, h974, h976, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                        · linarith only [h868, h870, h972, h976, hc35, hlam, hphi, u3ehi2]
                    · linarith only [h0, h868, h963, h972, h973, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                  · linarith only [h0, h868, h972, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h981 | h981
            · rcases m.htr 0 3 5 (by decide) (by decide) with h982 | h982
              · linarith only [h868, h870, h982, hlam]
              · linarith only [h981, h982, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h985 | h985
              · linarith only [h981, h985, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h987 | h987
                · linarith only [h0, h869, h963, h987, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h989 | h989
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h990 | h990
                    · linarith only [h0, h868, h963, h989, h990, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h868, h989, h990, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h868, h989, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
        · linarith only [h0, h869, h962, hlam]
      · linarith only [h0, h868, h961, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h996 | h996
    · rcases m.htr 0 2 3 (by decide) (by decide) with h997 | h997
      · rcases m.htr 0 2 4 (by decide) (by decide) with h998 | h998
        · rcases m.htr 0 2 5 (by decide) (by decide) with h999 | h999
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1000 | h1000
            · linarith only [h1000, h868, h869, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1002 | h1002
              · linarith only [h1000, h1002, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1004 | h1004
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1005 | h1005
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1006 | h1006
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1007 | h1007
                      · linarith only [h1000, h1007, h868, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                      · linarith only [h1005, h1007, h868, h869, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h0, h1005, h1006, h868, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1005, h868, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1004, h868, h869, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h869, h996, h998, h999, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1014 | h1014
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1015 | h1015
            · linarith only [h0, h1015, h868, h998, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1017 | h1017
              · linarith only [h1015, h1017, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1019 | h1019
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1020 | h1020
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1021 | h1021
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1022 | h1022
                      · linarith only [h1015, h1022, h868, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                      · linarith only [h1020, h1022, h868, h869, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h0, h1020, h1021, h868, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1020, h868, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1019, h868, h869, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h1014, h996, hlam]
      · linarith only [h0, h868, h997, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1030 | h1030
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1031 | h1031
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1032 | h1032
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1033 | h1033
            · linarith only [h1033, h868, h869, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1035 | h1035
              · linarith only [h1033, h1035, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1037 | h1037
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1038 | h1038
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1039 | h1039
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1040 | h1040
                      · linarith only [h1031, h1033, h1037, h1040, h868, h996, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                      · linarith only [h1038, h1040, h868, h869, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h0, h1032, h1038, h1039, h868, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                  · linarith only [h0, h1038, h868, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1037, h868, h869, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1046 | h1046
            · linarith only [h1046, h868, h869, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1048 | h1048
              · linarith only [h1046, h1048, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1050 | h1050
                · linarith only [h1031, h1032, h1050, hlam]
                · linarith only [h1050, h868, h869, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1053 | h1053
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1054 | h1054
            · linarith only [h0, h1031, h1054, h868, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1056 | h1056
              · linarith only [h1054, h1056, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1058 | h1058
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1059 | h1059
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1060 | h1060
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1061 | h1061
                      · linarith only [h1031, h1053, h1054, h1061, h868, h996, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h1059, h1061, h868, h869, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h0, h1059, h1060, h868, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1059, h868, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h0, h1031, h1058, h868, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1067 | h1067
            · linarith only [h0, h1031, h1067, h868, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1069 | h1069
              · linarith only [h1067, h1069, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1071 | h1071
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1072 | h1072
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1073 | h1073
                    · linarith only [h0, h1053, h1072, h1073, h868, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h1072, h1073, h868, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1072, h868, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1071, h868, h869, hc45, hlam, hphi, ht34, u3ehi1]
      · linarith only [h0, h1030, h868, hlam]

set_option maxHeartbeats 4588000 in
set_option maxHeartbeats 4588000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h868 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1079 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1080 | h1080
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1081 | h1081
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1082 | h1082
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1083 | h1083
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1084 | h1084
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1085 | h1085
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1086 | h1086
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1087 | h1087
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1088 | h1088
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1089 | h1089
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1090 | h1090
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1091 | h1091
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1092 | h1092
                          · linarith only [h1081, h1092, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                          · linarith only [h1084, h1092, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                        · linarith only [h1079, h1086, h1089, h1091, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · linarith only [h1079, h1089, h1090, h868, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1079, h1084, h1089, h868, hlam]
                  · linarith only [h0, h1083, h1088, hlam]
                · linarith only [h0, h1081, h1087, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1100 | h1100
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1101 | h1101
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1102 | h1102
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1103 | h1103
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1104 | h1104
                        · linarith only [h1079, h1086, h1104, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1106 | h1106
                          · linarith only [h1081, h1106, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                          · linarith only [h1079, h1086, h1102, h1106, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h1079, h1102, h1103, h868, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1080, h1084, h1086, h1102, h868, hlam]
                  · linarith only [h0, h1083, h1101, hlam]
                · linarith only [h0, h1081, h1100, hlam]
            · linarith only [h1084, h1085, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1079, h1084, h868, hlam]
        · linarith only [h0, h1080, h1083, hlam]
      · linarith only [h1079, h1081, h1082, h868, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1117 | h1117
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1118 | h1118
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1119 | h1119
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1120 | h1120
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1121 | h1121
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1122 | h1122
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1123 | h1123
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1124 | h1124
                    · linarith only [h0, h1079, h1081, h1122, h1124, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h1119, h1124, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h0, h1081, h1122, h1123, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1128 | h1128
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1129 | h1129
                    · linarith only [h0, h1079, h1122, h1129, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h1079, h1120, h1121, h1129, h868, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h1118, h1128, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1133 | h1133
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1134 | h1134
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1135 | h1135
                    · linarith only [h0, h1079, h1081, h1133, h1135, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h1081, h1119, h1133, h1135, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h1080, h1081, h1119, h1121, h1133, h1134, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1139 | h1139
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1140 | h1140
                    · linarith only [h0, h1079, h1133, h1140, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h1079, h1119, h1140, h868, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1080, h1118, h1119, h1121, h1139, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
            · linarith only [h1119, h1120, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h1079, h1081, h1119, hlam]
        · linarith only [h0, h1080, h1118, hlam]
      · linarith only [h0, h1079, h1117, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1148 | h1148
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1149 | h1149
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1150 | h1150
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1151 | h1151
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1152 | h1152
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1153 | h1153
              · linarith only [h1079, h1080, h1153, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1155 | h1155
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1156 | h1156
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1157 | h1157
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1158 | h1158
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1159 | h1159
                        · linarith only [h1079, h1080, h1153, h1159, hlam]
                        · linarith only [h1079, h1080, h1157, h1159, hc45, hlam, hphi, ht34, u3ehi3]
                      · linarith only [h1148, h1152, h1158, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                    · linarith only [h1152, h1157, h868, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h1079, h1150, h1151, h1155, h1156, h868, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                · linarith only [h0, h1148, h1155, hlam]
            · linarith only [h1151, h1152, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1079, h1151, h868, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1168 | h1168
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1169 | h1169
            · linarith only [h1148, h1150, h1169, hlam]
            · linarith only [h1168, h1169, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1079, h1168, h868, hlam]
      · linarith only [h0, h1079, h1149, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1174 | h1174
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1175 | h1175
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1176 | h1176
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1177 | h1177
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1178 | h1178
              · linarith only [h1079, h1080, h1178, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1180 | h1180
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1181 | h1181
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1182 | h1182
                    · linarith only [h1079, h1080, h1148, h1175, h1180, h1182, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h1080, h1148, h1175, h1176, h1180, h1182, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h1148, h1175, h1180, h1181, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1186 | h1186
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1187 | h1187
                    · linarith only [h0, h1079, h1180, h1187, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h1176, h1178, h1187, h868, hc45, hlam, hphi, ht34, u3ehi0]
                  · linarith only [h0, h1079, h1148, h1175, h1176, h1186, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
            · linarith only [h1176, h1177, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h1079, h1148, h1176, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1193 | h1193
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1194 | h1194
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1195 | h1195
              · linarith only [h0, h1079, h1175, h1195, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1197 | h1197
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1198 | h1198
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1199 | h1199
                    · linarith only [h0, h1079, h1148, h1197, h1199, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h1079, h1148, h1193, h1197, h1199, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1079, h1148, h1193, h1197, h1198, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1203 | h1203
                  · linarith only [h0, h1079, h1175, h1193, h1197, h1203, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1205 | h1205
                    · linarith only [h0, h1079, h1197, h1205, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h1079, h1193, h1205, h868, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
            · linarith only [h1193, h1194, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1079, h1193, h868, hlam]
      · linarith only [h0, h1079, h1174, hlam]

set_option maxHeartbeats 4588000 in
set_option maxHeartbeats 4588000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h868 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1079 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1211 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1212 | h1212
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1213 | h1213
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1214 | h1214
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1215 | h1215
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1216 | h1216
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1217 | h1217
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1218 | h1218
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1219 | h1219
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1220 | h1220
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1221 | h1221
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1222 | h1222
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1223 | h1223
                        · linarith only [h1212, h1223, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h1215, h1223, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                      · linarith only [h1079, h1211, h1221, h1222, hc45, hlam, hphi, ht34, u3ehi4]
                    · linarith only [h1215, h1221, h868, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1215, h1220, h868, hlam]
                · linarith only [h0, h1214, h1219, hlam]
              · linarith only [h0, h1212, h1218, hlam]
            · linarith only [h1079, h1211, h1217, hlam]
          · linarith only [h1215, h1216, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1233 | h1233
          · linarith only [h1215, h1233, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1211, h1233, h868, hlam]
      · linarith only [h0, h1211, h1214, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1237 | h1237
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1238 | h1238
        · linarith only [h1212, h1213, h1238, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1240 | h1240
          · linarith only [h1238, h1240, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1211, h1240, h868, hlam]
      · linarith only [h0, h1211, h1237, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1244 | h1244
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1245 | h1245
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1246 | h1246
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1247 | h1247
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1248 | h1248
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1249 | h1249
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1250 | h1250
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1251 | h1251
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1252 | h1252
                    · linarith only [h1079, h1211, h1212, h1244, h1249, h1252, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h1246, h1252, h868, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1212, h1244, h1246, h1249, h1251, hlam]
                · linarith only [h1079, h1211, h1212, h1244, h1247, h1249, h1250, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1257 | h1257
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1258 | h1258
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1259 | h1259
                    · linarith only [h0, h1211, h1249, h1259, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h1246, h1259, h868, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1246, h1258, h868, hlam]
                · linarith only [h0, h1245, h1257, hlam]
            · linarith only [h1079, h1211, h1248, hlam]
          · linarith only [h1246, h1247, hc35, hlam, hphi, u3ehi3]
        · linarith only [h1212, h1244, h1246, hlam]
      · linarith only [h0, h1211, h1245, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1268 | h1268
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1269 | h1269
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1270 | h1270
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1271 | h1271
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1272 | h1272
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1273 | h1273
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1274 | h1274
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1275 | h1275
                    · linarith only [h0, h1211, h1212, h1272, h1275, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h1269, h1275, h868, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1212, h1269, h1272, h1274, hlam]
                · linarith only [h1212, h1269, h1272, h1273, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1280 | h1280
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1281 | h1281
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1282 | h1282
                    · linarith only [h0, h1211, h1272, h1282, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h1269, h1282, h868, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1269, h1281, h868, hlam]
                · linarith only [h0, h1211, h1268, h1270, h1280, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
            · linarith only [h0, h1211, h1244, h1271, hlam]
          · linarith only [h1269, h1270, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1289 | h1289
          · linarith only [h1269, h1289, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1211, h1289, h868, hlam]
      · linarith only [h0, h1211, h1268, hlam]

end R2N4
