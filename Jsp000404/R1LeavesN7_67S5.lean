import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_M_LI_L_R_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0bigk := hb0.2.2.2
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h9, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h3, h9, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
                  · linarith only [h0, h12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h12, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h15 | h15
                · linarith only [h15, h6, h7, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                  · linarith only [h0, h17, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h17, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h20 | h20
              · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
                · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h22, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h22, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · linarith only [h20, h21, h6, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
                · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                  · linarith only [h0, h27, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h27, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
                  · linarith only [h0, h30, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h3, h30, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
          · linarith only [h3, h5, hc25, hlam, hphi, u2ehi2]
        · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h35 | h35
        · linarith only [h3, h35, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h37 | h37
          · linarith only [h3, h37, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h39 | h39
            · rcases m.htr 0 3 5 (by decide) (by decide) with h40 | h40
              · rcases m.htr 0 4 5 (by decide) (by decide) with h41 | h41
                · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
                  · linarith only [h0, h3, h42, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
                    · linarith only [h0, h37, h44, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h46 | h46
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h47 | h47
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h48 | h48
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h49 | h49
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h50 | h50
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h51 | h51
                                · linarith only [h1, h46, h51, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · rcases h0bigk with h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p53_1, u0elo0, u2ehi0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h1, h47, hc35, hlam, hphi, ht0b, ht5b, p53_1, u0elo0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h41, h51, hc34, hlam, hphi, ht0b, ht45, ht5b, p53_1, u0elo0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h0, h37, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p53_1, u0elo0, u2ehi1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h0, hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h3, hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h35, hlam, p53_1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h37, hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h1, hlam, p53_1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p53_1, u0elo2, u2ehi1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h1, h41, h51, hc34, hlam, hphi, ht0b, ht45, ht5b, p53_1, u0elo0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h0, h1, h37, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p53_1, u0elo0, u2ehi1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p53_1, u0elo3, u2ehi1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p53_1, u0elo3, u2ehi1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h39, hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h0, h1, h37, h39, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p53_1, u0elo0, u2ehi1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h2, hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p53_1, u0elo4, u2ehi1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h40, hlam, p53_0]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [h41, hlam, p53_1]
                                  · have p53_0 := h53c.1
                                    have p53_1 := h53c.2.1
                                    have p53_2 := h53c.2.2.1
                                    have p53_3 := h53c.2.2.2
                                    linarith only [hlam, p53_0]
                              · linarith only [h0, h35, h50, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                            · linarith only [h0, h3, h49, hc35, hlam, hphi, ht23, u2ehi1]
                          · linarith only [h0, h3, h48, hc34, hlam, hphi, ht23, u2ehi1]
                        · linarith only [h40, h46, h47, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h1, h39, h42, h46, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
                  · linarith only [h0, h35, h84, hc24, hlam, hphi, u2ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h86 | h86
                    · linarith only [h0, h37, h86, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h90 | h90
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h91 | h91
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h92 | h92
                              · linarith only [h0, h35, h41, h92, hc24, hlam, hphi, u2ehi1]
                              · linarith only [h0, h35, h92, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                            · linarith only [h1, h3, h89, h91, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h0, h1, h3, h88, h90, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                        · linarith only [h40, h88, h89, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h1, h39, h84, h88, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h99 | h99
                · linarith only [h39, h40, h99, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
                  · linarith only [h0, h101, h3, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h103 | h103
                    · linarith only [h0, h103, h37, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h105 | h105
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h106 | h106
                        · linarith only [h1, h106, h40, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h108 | h108
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h109 | h109
                            · linarith only [h0, h109, h35, h39, h40, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h0, h109, h3, hc35, hlam, hphi, ht23, u2ehi1]
                          · linarith only [h0, h1, h105, h108, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
                      · linarith only [h105, h39, h40, hc13, hc35, hlam, hphi]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h114 | h114
              · rcases m.htr 0 4 5 (by decide) (by decide) with h115 | h115
                · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
                  · linarith only [h0, h116, h3, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h118 | h118
                    · linarith only [h0, h118, h37, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h120 | h120
                      · linarith only [h1, h120, h39, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h122 | h122
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
                          · linarith only [h0, h114, h123, h37, h39, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h0, h123, h3, hc34, hlam, hphi, ht23, u2ehi1]
                        · linarith only [h114, h122, h39, hc13, hc34, hlam, hphi]
                · linarith only [h114, h115, h39, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h128 | h128
                · rcases m.htr 1 2 3 (by decide) (by decide) with h129 | h129
                  · linarith only [h0, h129, h3, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h131 | h131
                    · linarith only [h0, h131, h37, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h133 | h133
                      · linarith only [h0, h1, h133, h3, h39, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h135 | h135
                        · linarith only [h1, h114, h135, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h137 | h137
                          · linarith only [h0, h137, h3, h39, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h0, h137, h3, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h140 | h140
                  · linarith only [h0, h140, h3, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h142 | h142
                    · linarith only [h0, h142, h37, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h144 | h144
                      · linarith only [h1, h144, h39, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h146 | h146
                        · linarith only [h1, h114, h146, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h148 | h148
                          · linarith only [h0, h148, h3, h39, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h0, h148, h3, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h151 | h151
      · rcases m.htr 0 2 4 (by decide) (by decide) with h152 | h152
        · rcases m.htr 0 2 5 (by decide) (by decide) with h153 | h153
          · linarith only [h0, h153, h2, hlam]
          · linarith only [h151, h153, hc25, hlam, hphi, u2ehi2]
        · linarith only [h151, h152, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h157 | h157
        · linarith only [h151, h157, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h159 | h159
          · linarith only [h151, h159, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h161 | h161
            · rcases m.htr 0 3 5 (by decide) (by decide) with h162 | h162
              · linarith only [h1, h162, h2, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h164 | h164
                · linarith only [h0, h161, h162, h164, h2, hc35, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
                  · linarith only [h0, h166, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h168 | h168
                    · linarith only [h1, h159, h166, h168, h2, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h168, h2, hc25, hlam, hphi, u2ehi1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h171 | h171
              · linarith only [h0, h161, h171, h2, hc34, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h173 | h173
                · rcases m.htr 1 2 3 (by decide) (by decide) with h174 | h174
                  · linarith only [h0, h151, h174, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h176 | h176
                    · linarith only [h1, h174, h176, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi4]
                    · linarith only [h1, h174, h176, h2, hc25, hlam, hphi, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
                  · linarith only [h0, h151, h179, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h181 | h181
                    · linarith only [h1, h179, h181, h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4, u2ehi4]
                    · linarith only [h1, h179, h181, h2, hc25, hlam, hphi, u2ehi1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h184 | h184
    · rcases m.htr 0 2 3 (by decide) (by decide) with h185 | h185
      · linarith only [h0, h1, h185, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h187 | h187
        · linarith only [h185, h187, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h189 | h189
          · linarith only [h185, h189, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h191 | h191
            · rcases m.htr 0 3 5 (by decide) (by decide) with h192 | h192
              · rcases m.htr 0 4 5 (by decide) (by decide) with h193 | h193
                · rcases m.htr 1 2 3 (by decide) (by decide) with h194 | h194
                  · linarith only [h0, h1, h185, h194, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                  · linarith only [h0, h1, h194, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h197 | h197
                  · linarith only [h0, h197, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h1, h197, hc23, hlam, hphi, u2ehi1]
              · linarith only [h0, h1, h192, hc35, hlam, hphi, ht23, u2ehi1]
            · linarith only [h0, h1, h191, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h202 | h202
      · linarith only [h0, h1, h202, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h204 | h204
        · linarith only [h202, h204, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h206 | h206
          · linarith only [h202, h206, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h208 | h208
            · rcases m.htr 0 3 5 (by decide) (by decide) with h209 | h209
              · rcases m.htr 0 4 5 (by decide) (by decide) with h210 | h210
                · rcases m.htr 1 2 3 (by decide) (by decide) with h211 | h211
                  · linarith only [h0, h184, h202, h208, h210, h211, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                  · linarith only [h0, h1, h211, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h214 | h214
                  · linarith only [h0, h184, h209, h214, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                  · linarith only [h0, h1, h214, hc23, hlam, hphi, u2ehi1]
              · linarith only [h0, h1, h209, hc35, hlam, hphi, ht23, u2ehi1]
            · linarith only [h0, h1, h208, hc34, hlam, hphi, ht23, u2ehi1]

theorem r1l7_20_12_13_M_LI_L_R_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h219 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0bigk := hb0.2.2.2
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h220 | h220
  · rcases m.htr 0 2 3 (by decide) (by decide) with h221 | h221
    · rcases m.htr 0 2 4 (by decide) (by decide) with h222 | h222
      · rcases m.htr 0 2 5 (by decide) (by decide) with h223 | h223
        · rcases m.htr 0 3 4 (by decide) (by decide) with h224 | h224
          · rcases m.htr 0 3 5 (by decide) (by decide) with h225 | h225
            · rcases m.htr 0 4 5 (by decide) (by decide) with h226 | h226
              · rcases m.htr 1 2 3 (by decide) (by decide) with h227 | h227
                · rcases m.htr 1 2 5 (by decide) (by decide) with h228 | h228
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h229 | h229
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h230 | h230
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h231 | h231
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h232 | h232
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h233 | h233
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h234 | h234
                              · linarith only [h219, h227, h231, h234, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h0, h219, h227, h231, h233, h234, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h226, h233, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                          · linarith only [h0, h219, h225, h232, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                        · linarith only [h0, h219, h224, h231, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                      · linarith only [h0, h219, h225, h229, h230, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h0, h219, h224, h227, h229, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                  · linarith only [h0, h219, h227, h228, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h223, h227, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h244 | h244
                · rcases m.htr 1 2 5 (by decide) (by decide) with h245 | h245
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h246 | h246
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h247 | h247
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h248 | h248
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h249 | h249
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h250 | h250
                            · linarith only [h222, h226, h250, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h252 | h252
                              · linarith only [h0, h219, h222, h226, h244, h248, h252, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases h0bigk with h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h0, hlam, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h0, h219, h244, h249, h252, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h0, h222, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p254_1, u2ehi3]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h0, h220, h245, h250, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p254_1, u2ehi3]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h219, h245, h247, h250, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p254_1, u0elo1, u2ehi3]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h219, h245, h247, h250, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p254_1, u0elo1, u2ehi3]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h222, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p254_1, u0elo1, u2ehi3]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h220, h245, h250, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p254_1, u0elo1, u2ehi3]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h219, hlam, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h221, hlam, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h222, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p254_1, u0elo2, u2ehi3]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h0, h219, h220, h245, h250, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p254_1, u2ehi3]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h226, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h222, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h224, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h226, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h220, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h223, hlam, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h225, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h222, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p254_1, u0elo4, u2ehi3]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [hlam, p254_0]
                          · linarith only [h225, h249, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                        · linarith only [h224, h248, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                      · linarith only [h225, h246, h247, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h0, h219, h224, h244, h246, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h219, h244, h245, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h223, h244, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h286 | h286
              · linarith only [h224, h225, h286, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h288 | h288
                · rcases m.htr 1 2 5 (by decide) (by decide) with h289 | h289
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h290 | h290
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h291 | h291
                      · linarith only [h0, h219, h222, h224, h225, h291, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h293 | h293
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h294 | h294
                          · linarith only [h219, h225, h288, h294, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h296 | h296
                            · linarith only [h222, h286, h296, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h298 | h298
                              · linarith only [h219, h222, h286, h288, h293, h298, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi3]
                              · rcases h0bigk with h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h0, hlam, p300_1]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h0, h219, h288, h293, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p300_1]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h0, h222, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h0, h219, h225, h288, h293, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h219, h288, h293, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u0elo1, u2ehi3]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h219, h288, h293, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u0elo1, u2ehi3]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h222, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u0elo1, u2ehi3]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h219, h225, h288, h293, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u0elo1, u2ehi3]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h219, hlam, p300_1]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h221, hlam, p300_1]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h222, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u0elo2, u2ehi3]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h225, hlam, p300_1]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h220, h289, h293, h294, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u0elo3, u2ehi3]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h222, hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h224, hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h286, hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h220, hlam, p300_0]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h223, hlam, p300_1]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h0, h219, h220, h288, h293, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [h0, h220, h222, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                · have p300_0 := h300c.1
                                  have p300_1 := h300c.2.1
                                  have p300_2 := h300c.2.2.1
                                  have p300_3 := h300c.2.2.2
                                  linarith only [hlam, p300_0]
                        · linarith only [h224, h293, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                    · linarith only [h224, h225, h290, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h219, h288, h289, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h220, h221, h222, h224, h225, h288, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h330 | h330
            · rcases m.htr 0 4 5 (by decide) (by decide) with h331 | h331
              · rcases m.htr 1 2 3 (by decide) (by decide) with h332 | h332
                · rcases m.htr 1 2 5 (by decide) (by decide) with h333 | h333
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h334 | h334
                    · linarith only [h219, h224, h334, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h336 | h336
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h337 | h337
                        · linarith only [h219, h224, h332, h337, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h339 | h339
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h340 | h340
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h341 | h341
                              · rcases h0bigk with h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [hlam, p342_0]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h0, hlam, p342_1]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h0, h219, h332, h339, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p342_1]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h0, h220, h224, h330, h333, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p342_1, u2ehi4]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h0, h220, h333, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p342_1, u2ehi4]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h219, h333, h336, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p342_1, u0elo1, u2ehi4]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [hlam, p342_0]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h220, h330, h333, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p342_1, u0elo1, u2ehi4]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h220, h224, h330, h333, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p342_1, u0elo1, u2ehi4]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h220, h333, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p342_1, u0elo1, u2ehi4]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h219, hlam, p342_1]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h221, hlam, p342_1]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [hlam, p342_0]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h224, hlam, p342_1]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h220, h333, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p342_1, u0elo2, u2ehi4]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h219, h222, h333, h336, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p342_1, u0elo1, u2ehi4]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h222, hlam, p342_0]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h219, h222, h333, h336, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p342_1, u0elo1, u2ehi4]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [hlam, p342_0]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h220, h222, h333, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p342_1, u0elo1, u2ehi4]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h220, hlam, p342_0]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h223, hlam, p342_1]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h330, hlam, p342_0]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [h331, hlam, p342_1]
                                · have p342_0 := h342c.1
                                  have p342_1 := h342c.2.1
                                  have p342_2 := h342c.2.2.1
                                  have p342_3 := h342c.2.2.2
                                  linarith only [hlam, p342_0]
                              · linarith only [h219, h224, h333, h336, h341, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                            · linarith only [h224, h330, h331, h337, h339, h340, hc34, hlam, hphi, ht23, u2ehi4]
                          · linarith only [h224, h330, h339, hc23, hc34, hlam, hphi]
                      · linarith only [h224, h330, h336, hc13, hc34, hlam, hphi]
                  · linarith only [h0, h219, h332, h333, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h223, h332, hc23, hlam, hphi, u2ehi4]
              · linarith only [h224, h330, h331, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h375 | h375
              · rcases m.htr 1 2 3 (by decide) (by decide) with h376 | h376
                · rcases m.htr 1 2 5 (by decide) (by decide) with h377 | h377
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h378 | h378
                    · linarith only [h219, h224, h378, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h380 | h380
                      · linarith only [h219, h330, h380, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h382 | h382
                        · linarith only [h219, h224, h376, h382, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h384 | h384
                          · linarith only [h219, h330, h376, h384, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h386 | h386
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h387 | h387
                              · rcases h0bigk with h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [hlam, p388_0]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h0, hlam, p388_1]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h0, h219, h376, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p388_1, u2ehi2]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h0, h220, h375, h377, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p388_1, u2ehi4]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h0, h220, h377, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p388_1, u2ehi4]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h219, h376, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p388_1, u0elo1, u2ehi2]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [hlam, p388_0]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h219, h376, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p388_1, u0elo1, u2ehi2]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h220, h375, h377, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p388_1, u0elo1, u2ehi4]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h220, h377, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p388_1, u0elo1, u2ehi4]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h219, hlam, p388_1]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h221, hlam, p388_1]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [hlam, p388_0]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h224, hlam, p388_1]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h330, hlam, p388_1]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h220, h376, h380, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p388_1, u0elo3, u2ehi2]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h222, hlam, p388_0]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h219, h376, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p388_1, u0elo3, u2ehi2]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [hlam, p388_0]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h219, h222, h330, h376, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p388_1, u0elo1, u2ehi2]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h220, hlam, p388_0]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h223, hlam, p388_1]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h219, h376, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p388_1, u0elo4, u2ehi2]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [h375, hlam, p388_1]
                                · have p388_0 := h388c.1
                                  have p388_1 := h388c.2.1
                                  have p388_2 := h388c.2.2.1
                                  have p388_3 := h388c.2.2.2
                                  linarith only [hlam, p388_0]
                              · linarith only [h219, h224, h376, h387, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · linarith only [h375, h386, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                  · linarith only [h0, h219, h376, h377, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h220, h221, h330, h376, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h418 | h418
                · rcases m.htr 1 2 5 (by decide) (by decide) with h419 | h419
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h420 | h420
                    · linarith only [h219, h224, h420, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h422 | h422
                      · linarith only [h219, h220, h224, h330, h419, h422, hc34, hlam, hphi, ht23, u2ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h424 | h424
                        · linarith only [h219, h221, h224, h424, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h426 | h426
                          · linarith only [h219, h330, h418, h426, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h428 | h428
                            · linarith only [h222, h375, h428, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h430 | h430
                              · linarith only [h219, h224, h375, h418, h430, hc34, hlam, hphi, ht23, u2ehi2]
                              · linarith only [h219, h224, h418, h430, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h219, h418, h419, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h223, h418, hc23, hlam, hphi, u2ehi4]
        · linarith only [h221, h223, hc25, hlam, hphi, u2ehi2]
      · linarith only [h221, h222, hc24, hlam, hphi, u2ehi2]
    · linarith only [h0, h219, h221, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h438 | h438
    · rcases m.htr 0 2 4 (by decide) (by decide) with h439 | h439
      · rcases m.htr 0 2 5 (by decide) (by decide) with h440 | h440
        · rcases m.htr 0 3 4 (by decide) (by decide) with h441 | h441
          · rcases m.htr 0 3 5 (by decide) (by decide) with h442 | h442
            · linarith only [h219, h220, h442, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h444 | h444
              · linarith only [h219, h220, h441, h444, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h446 | h446
                · rcases m.htr 1 2 5 (by decide) (by decide) with h447 | h447
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h448 | h448
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h449 | h449
                      · linarith only [h219, h442, h449, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h219, h220, h446, h449, hc35, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h441, h446, h448, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                  · linarith only [h440, h447, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                · linarith only [h0, h440, h446, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h455 | h455
            · linarith only [h219, h220, h455, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h457 | h457
              · rcases m.htr 1 2 3 (by decide) (by decide) with h458 | h458
                · rcases m.htr 1 2 5 (by decide) (by decide) with h459 | h459
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h460 | h460
                    · linarith only [h219, h441, h460, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h462 | h462
                      · linarith only [h219, h220, h455, h462, hlam]
                      · linarith only [h219, h220, h458, h462, hc35, hlam, hphi, ht23, u2ehi2]
                  · linarith only [h440, h459, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                · linarith only [h0, h440, h458, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h467 | h467
                · rcases m.htr 1 2 5 (by decide) (by decide) with h468 | h468
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h469 | h469
                    · linarith only [h219, h441, h469, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h471 | h471
                      · linarith only [h219, h455, h471, hlam]
                      · linarith only [h219, h220, h467, h471, hc35, hlam, hphi, ht23, u2ehi2]
                  · linarith only [h440, h468, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                · linarith only [h0, h440, h467, hc23, hlam, hphi, u2ehi4]
        · linarith only [h438, h440, hc25, hlam, hphi, u2ehi2]
      · linarith only [h438, h439, hc24, hlam, hphi, u2ehi2]
    · linarith only [h0, h219, h438, hlam]

end R2N4
