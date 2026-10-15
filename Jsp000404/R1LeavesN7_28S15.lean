import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10642000 in
set_option maxHeartbeats 10642000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h5ehi := hb5.1
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
    · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h0, h10, h12, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h10, h11, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
                  · linarith only [h0, h10, h16, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h18 | h18
                    · linarith only [h0, h10, h18, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                        · linarith only [h1, h21, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h0, h20, h21, h4, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h24 | h24
                        · linarith only [h0, h20, h24, h4, h7, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                          · linarith only [h2, h26, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                            · linarith only [h0, h10, h20, h28, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h0, h10, h28, h4, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h33 | h33
                    · linarith only [h0, h33, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h0, h31, h33, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h31, h32, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h37 | h37
                  · linarith only [h0, h31, h37, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h39 | h39
                    · linarith only [h0, h31, h39, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h42 | h42
                        · linarith only [h1, h42, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h0, h4, h41, h42, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h45 | h45
                        · linarith only [h1, h45, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h47 | h47
                          · linarith only [h2, h47, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
                            · linarith only [h0, h4, h41, h49, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h31, h49, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h52 | h52
              · linarith only [h52, h7, h8, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
                    · linarith only [h0, h56, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h55, h56, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h5, h54, h55, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
                  · linarith only [h0, h4, h54, h60, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h62 | h62
                    · linarith only [h0, h4, h54, h62, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h64 | h64
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h65 | h65
                        · linarith only [h1, h65, h8, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h67 | h67
                          · linarith only [h2, h67, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
                              · linarith only [h0, h4, h5, h60, h7, h70, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h72 | h72
                                · linarith only [h5, h52, h72, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h74 | h74
                                  · linarith only [h5, h52, h60, h64, h74, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                  · rcases h0bigk with h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [hlam, p76_0]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h6, h62, hlam, hphi, ht0b, ht5b, p76_1, u0elo0, u5ehi1]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h5, h60, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1, u0elo0]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h5, h60, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1, u0elo0]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [hlam, hphi, ht0b, ht5b, p76_1, u0elo0, u5ehi0]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h0, hlam, p76_0]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [hlam, p76_0]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h5, h60, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1, u0elo1]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h0, h5, h60, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1, u0elo0]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h0, h3, hlam, hphi, ht0b, ht5b, p76_1, u0elo0, u5ehi1]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h1, hlam, p76_1]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h4, hlam, p76_1]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [hlam, p76_0]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h5, h60, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1, u0elo2]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h8, hlam, p76_1]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h2, hlam, p76_0]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h5, hlam, p76_0]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h7, hlam, p76_0]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [hlam, p76_0]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h52, hlam, p76_0]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h3, hlam, p76_0]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h6, hlam, p76_1]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h1, h64, hc34, hlam, hphi, ht0b, ht45, ht5b, p76_1, u0elo4]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [h0, h5, h6, h60, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1, u0elo0]
                                    · have p76_0 := h76c.1
                                      have p76_1 := h76c.2.1
                                      have p76_2 := h76c.2.2.1
                                      have p76_3 := h76c.2.2.2
                                      linarith only [hlam, p76_0]
                            · linarith only [h1, h64, h69, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h54, h64, h7, h8, hc12, hc35, hlam, hphi, ht23]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h104 | h104
            · rcases m.htr 0 4 5 (by decide) (by decide) with h105 | h105
              · rcases m.htr 1 2 3 (by decide) (by decide) with h106 | h106
                · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h108 | h108
                    · linarith only [h0, h108, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h0, h107, h108, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h0, h106, h107, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h112 | h112
                  · linarith only [h0, h106, h112, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h114 | h114
                    · linarith only [h0, h106, h114, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h116 | h116
                      · linarith only [h104, h116, h7, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h118 | h118
                        · linarith only [h1, h118, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h104, h118, h7, hc13, hc34, hlam, hphi]
              · linarith only [h104, h105, h7, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h122 | h122
              · rcases m.htr 1 2 3 (by decide) (by decide) with h123 | h123
                · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h125 | h125
                    · linarith only [h0, h125, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h0, h123, h125, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h123, h124, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
                  · linarith only [h0, h123, h129, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h131 | h131
                    · linarith only [h0, h123, h131, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h133 | h133
                      · linarith only [h1, h133, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h135 | h135
                        · linarith only [h1, h104, h135, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h137 | h137
                          · linarith only [h137, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h139 | h139
                            · linarith only [h0, h122, h139, h4, h7, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h141 | h141
                              · linarith only [h104, h141, h4, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h143 | h143
                                · linarith only [h0, h123, h133, h137, h143, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                · linarith only [h122, h129, h143, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h146 | h146
                · rcases m.htr 1 2 4 (by decide) (by decide) with h147 | h147
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h148 | h148
                    · linarith only [h0, h148, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h0, h146, h148, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h146, h147, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h152 | h152
                  · linarith only [h0, h146, h152, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h154 | h154
                    · linarith only [h0, h146, h154, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h156 | h156
                      · linarith only [h1, h156, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h158 | h158
                        · linarith only [h1, h158, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h160 | h160
                          · linarith only [h122, h160, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h162 | h162
                            · linarith only [h162, h4, h7, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h164 | h164
                              · linarith only [h104, h164, h4, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h166 | h166
                                · linarith only [h0, h122, h146, h166, h4, h5, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h168 | h168
                                  · linarith only [h122, h146, h168, h4, h7, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h146, h168, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h171 | h171
          · rcases m.htr 0 3 5 (by decide) (by decide) with h172 | h172
            · linarith only [h172, h4, h6, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h174 | h174
              · linarith only [h171, h174, h4, h6, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h176 | h176
                · rcases m.htr 1 2 4 (by decide) (by decide) with h177 | h177
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h178 | h178
                    · linarith only [h0, h178, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h180 | h180
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h181 | h181
                        · linarith only [h1, h172, h181, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h183 | h183
                          · linarith only [h174, h183, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h185 | h185
                            · linarith only [h0, h176, h185, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h1, h172, h180, h185, hc23, hc35, hlam, hphi]
                      · linarith only [h171, h172, h180, hc13, hc35, hlam, hphi]
                  · linarith only [h177, h5, h6, hc12, hc25, hlam, hphi]
                · linarith only [h176, h4, h6, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h191 | h191
            · linarith only [h191, h4, h6, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h193 | h193
              · linarith only [h193, h5, h6, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
                · rcases m.htr 1 2 4 (by decide) (by decide) with h196 | h196
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h197 | h197
                    · linarith only [h0, h197, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h199 | h199
                      · linarith only [h1, h171, h199, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h201 | h201
                        · linarith only [h1, h191, h201, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h203 | h203
                          · linarith only [h193, h2, h203, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h205 | h205
                            · linarith only [h0, h195, h205, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h207 | h207
                              · linarith only [h191, h196, h197, h205, h207, h3, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h209 | h209
                                · linarith only [h196, h197, h209, h3, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h211 | h211
                                  · linarith only [h209, h211, h4, h6, hc23, hc34, hlam, hphi]
                                  · rcases h0bigk with h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [hlam, p213_0]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [h0, h196, h205, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p213_1, u0elo0]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      rcases p213_3 (m.d 0 1) (by simp) with h216 | h216
                                      · rcases p213_3 (m.d 0 2) (by simp) with h217 | h217
                                        · linarith only [h0, h217, hlam]
                                        · linarith only [h217, h4, hlam]
                                      · linarith only [h1, h216, hlam]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      rcases p213_3 (m.d 0 1) (by simp) with h221 | h221
                                      · rcases p213_3 (m.d 0 2) (by simp) with h222 | h222
                                        · linarith only [h0, h222, hlam]
                                        · linarith only [h222, h5, hlam]
                                      · linarith only [h2, h221, hlam]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [h0, h196, h205, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p213_1, u0elo0]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [h0, hlam, p213_0]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [hlam, p213_0]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [h1, h195, h207, h6, hc23, hc35, hlam, hphi, p213_1]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [h207, h211, h6, hc04, hc45, hlam, hphi, p213_1]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [h6, hlam, p213_0]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [h1, hlam, p213_1]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [h4, hlam, p213_1]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [hlam, p213_0]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [h171, hlam, p213_1]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [h191, hlam, p213_1]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [h2, hlam, p213_0]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [h5, hlam, p213_0]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [h1, h195, h207, h211, h5, h6, hc23, hc45, hlam, hphi, ht34, p213_1]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [hlam, p213_0]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [h193, hlam, p213_0]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [h3, hlam, p213_0]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [h0, h196, h205, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p213_1, u0elo4]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      rcases p213_3 (m.d 0 1) (by simp) with h244 | h244
                                      · rcases p213_3 (m.d 0 2) (by simp) with h245 | h245
                                        · linarith only [h245, h6, hlam]
                                        · linarith only [h245, h4, hlam]
                                      · linarith only [h1, h244, hlam]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      rcases p213_3 (m.d 0 1) (by simp) with h249 | h249
                                      · rcases p213_3 (m.d 0 2) (by simp) with h250 | h250
                                        · linarith only [h250, h6, hlam]
                                        · linarith only [h250, h5, hlam]
                                      · linarith only [h2, h249, hlam]
                                    · have p213_0 := h213c.1
                                      have p213_1 := h213c.2.1
                                      have p213_2 := h213c.2.2.1
                                      have p213_3 := h213c.2.2.2
                                      linarith only [hlam, p213_0]
                  · linarith only [h196, h5, h6, hc12, hc25, hlam, hphi]
                · linarith only [h195, h4, h6, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h257 | h257
        · rcases m.htr 0 3 4 (by decide) (by decide) with h258 | h258
          · linarith only [h258, h4, h5, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h260 | h260
            · rcases m.htr 0 4 5 (by decide) (by decide) with h261 | h261
              · rcases m.htr 1 2 3 (by decide) (by decide) with h262 | h262
                · rcases m.htr 1 2 4 (by decide) (by decide) with h263 | h263
                  · linarith only [h0, h260, h263, h4, h5, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h265 | h265
                    · linarith only [h2, h263, h265, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h257, h262, h265, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h262, h4, h5, hc12, hc24, hlam, hphi]
              · linarith only [h260, h261, h4, h5, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h270 | h270
              · rcases m.htr 1 2 3 (by decide) (by decide) with h271 | h271
                · rcases m.htr 1 2 4 (by decide) (by decide) with h272 | h272
                  · linarith only [h0, h272, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h274 | h274
                    · linarith only [h2, h272, h274, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h257, h274, h5, hc12, hc24, hlam, hphi]
                · linarith only [h271, h4, h5, hc12, hc24, hlam, hphi]
              · linarith only [h257, h270, h5, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h279 | h279
          · linarith only [h279, h4, h5, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h281 | h281
            · linarith only [h257, h281, h4, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h283 | h283
              · rcases m.htr 1 2 3 (by decide) (by decide) with h284 | h284
                · rcases m.htr 1 2 4 (by decide) (by decide) with h285 | h285
                  · linarith only [h0, h285, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h287 | h287
                    · linarith only [h0, h257, h287, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h289 | h289
                      · linarith only [h1, h279, h289, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h291 | h291
                        · linarith only [h1, h281, h291, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
                          · linarith only [h2, h293, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · linarith only [h283, h284, h285, h293, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                · linarith only [h257, h284, h4, hc12, hc25, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h297 | h297
                · rcases m.htr 1 2 4 (by decide) (by decide) with h298 | h298
                  · linarith only [h0, h298, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h300 | h300
                    · linarith only [h0, h300, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h302 | h302
                      · linarith only [h1, h279, h302, h4, h5, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h304 | h304
                        · linarith only [h1, h281, h304, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h306 | h306
                          · linarith only [h2, h283, h306, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h308 | h308
                            · linarith only [h0, h279, h297, h308, h5, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h310 | h310
                              · linarith only [h0, h281, h283, h297, h310, h5, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h312 | h312
                                · linarith only [h0, h283, h297, h308, h312, h5, hc23, hc34, hlam, hphi]
                                · linarith only [h0, h297, h312, h5, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h297, h4, h5, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h316 | h316
      · rcases m.htr 0 2 5 (by decide) (by decide) with h317 | h317
        · rcases m.htr 0 3 4 (by decide) (by decide) with h318 | h318
          · rcases m.htr 0 3 5 (by decide) (by decide) with h319 | h319
            · rcases m.htr 0 4 5 (by decide) (by decide) with h320 | h320
              · rcases m.htr 1 2 3 (by decide) (by decide) with h321 | h321
                · linarith only [h316, h320, h321, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h323 | h323
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h324 | h324
                    · linarith only [h1, h321, h324, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h317, h324, h4, hc12, hc23, hlam, hphi]
                  · linarith only [h316, h323, h4, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h328 | h328
                · linarith only [h317, h328, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h330 | h330
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h331 | h331
                    · linarith only [h1, h328, h331, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h317, h331, h4, hc12, hc23, hlam, hphi]
                  · linarith only [h316, h330, h4, hc12, hc23, hlam, hphi]
            · linarith only [h317, h319, h4, hlam]
          · linarith only [h316, h318, h4, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h337 | h337
          · rcases m.htr 0 3 5 (by decide) (by decide) with h338 | h338
            · rcases m.htr 0 4 5 (by decide) (by decide) with h339 | h339
              · linarith only [h316, h317, h339, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h341 | h341
                · linarith only [h0, h341, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h343 | h343
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h344 | h344
                    · linarith only [h0, h317, h344, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h346 | h346
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h347 | h347
                        · linarith only [h1, h347, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h338, h341, h343, h347, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h1, h337, h341, h343, h346, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h316, h317, h343, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h352 | h352
              · linarith only [h316, h317, h352, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h354 | h354
                · linarith only [h0, h354, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h356 | h356
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h357 | h357
                    · linarith only [h0, h357, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h359 | h359
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h360 | h360
                        · linarith only [h1, h338, h360, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h362 | h362
                          · linarith only [h2, h352, h362, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h364 | h364
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h365 | h365
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h366 | h366
                                · linarith only [h0, h338, h352, h356, h366, h4, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h368 | h368
                                  · linarith only [h0, h338, h356, h364, h365, h366, h368, h4, hlam]
                                  · rcases h0bigk with h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [hlam, p370_0]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h0, h356, h364, hc34, hlam, hphi, ht0b, ht45, ht5b, p370_1, u0elo0]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h0, h356, h364, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, p370_1, u0elo0]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      rcases p370_3 (m.d 0 1) (by simp) with h374 | h374
                                      · rcases p370_3 (m.d 0 2) (by simp) with h375 | h375
                                        · linarith only [h0, h375, hlam]
                                        · linarith only [h316, h375, hlam]
                                      · linarith only [h2, h374, hlam]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h0, h338, h356, h364, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, p370_1, u0elo0]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h0, hlam, p370_0]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [hlam, p370_0]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h4, hlam, p370_0]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h2, h338, h356, h364, h365, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p370_1]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h317, hlam, p370_0]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h1, hlam, p370_1]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h338, h365, hc02, hc23, hlam, hphi, p370_1]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [hlam, p370_0]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h2, h338, h356, h364, h365, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p370_1]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h338, hlam, p370_1]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h2, hlam, p370_0]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h316, hlam, p370_0]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h337, hlam, p370_0]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [hlam, p370_0]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h352, hlam, p370_0]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h3, hlam, p370_0]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h0, h356, h364, hc34, hlam, hphi, ht0b, ht45, ht5b, p370_1, u0elo4]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [h0, h338, h356, h364, h365, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p370_1]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      rcases p370_3 (m.d 0 1) (by simp) with h398 | h398
                                      · rcases p370_3 (m.d 0 2) (by simp) with h399 | h399
                                        · linarith only [h317, h399, hlam]
                                        · linarith only [h316, h399, hlam]
                                      · linarith only [h2, h398, hlam]
                                    · have p370_0 := h370c.1
                                      have p370_1 := h370c.2.1
                                      have p370_2 := h370c.2.2.1
                                      have p370_3 := h370c.2.2.2
                                      linarith only [hlam, p370_0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h404 | h404
                                · linarith only [h0, h356, h404, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h406 | h406
                                  · linarith only [h0, h317, h356, h364, h365, h4, h404, h406, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                                  · linarith only [h0, h356, h365, h4, h406, hc24, hc45, hlam, hphi]
                            · linarith only [h0, h337, h356, h364, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h337, h338, h354, h356, h359, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h316, h356, h4, hc12, hc23, hlam, hphi]
          · linarith only [h316, h337, h4, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h413 | h413
        · rcases m.htr 0 3 4 (by decide) (by decide) with h414 | h414
          · rcases m.htr 0 3 5 (by decide) (by decide) with h415 | h415
            · rcases m.htr 0 4 5 (by decide) (by decide) with h416 | h416
              · rcases m.htr 1 2 3 (by decide) (by decide) with h417 | h417
                · linarith only [h0, h4, h413, h417, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h419 | h419
                  · linarith only [h316, h413, h419, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h421 | h421
                    · linarith only [h1, h417, h421, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h4, h413, h421, hc12, hc23, hlam, hphi]
              · linarith only [h316, h413, h416, hlam]
            · linarith only [h316, h413, h414, h415, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h426 | h426
            · rcases m.htr 0 4 5 (by decide) (by decide) with h427 | h427
              · rcases m.htr 1 2 3 (by decide) (by decide) with h428 | h428
                · linarith only [h4, h413, h428, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h430 | h430
                  · linarith only [h1, h316, h413, h428, h430, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h432 | h432
                    · linarith only [h1, h428, h432, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h4, h413, h432, hc12, hc23, hlam, hphi]
              · linarith only [h316, h413, h427, hlam]
            · linarith only [h4, h413, h426, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h437 | h437
          · rcases m.htr 0 3 5 (by decide) (by decide) with h438 | h438
            · rcases m.htr 0 4 5 (by decide) (by decide) with h439 | h439
              · rcases m.htr 1 2 3 (by decide) (by decide) with h440 | h440
                · linarith only [h0, h4, h440, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h442 | h442
                  · linarith only [h0, h316, h439, h442, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h444 | h444
                    · linarith only [h0, h413, h444, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h446 | h446
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h447 | h447
                        · linarith only [h1, h447, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h438, h446, h447, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h450 | h450
                        · linarith only [h1, h450, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h452 | h452
                          · linarith only [h1, h437, h446, h452, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h454 | h454
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h455 | h455
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h456 | h456
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h457 | h457
                                  · linarith only [h1, h437, h440, h446, h452, h457, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                  · linarith only [h439, h440, h446, h457, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                                · linarith only [h0, h1, h316, h437, h439, h456, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · linarith only [h4, h437, h440, h446, h455, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h4, h437, h439, h440, h446, h452, h454, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h463 | h463
                · linarith only [h0, h4, h438, h463, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h465 | h465
                  · linarith only [h0, h316, h465, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h467 | h467
                    · linarith only [h0, h413, h467, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h469 | h469
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h470 | h470
                        · linarith only [h1, h470, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h438, h469, h470, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h473 | h473
                        · linarith only [h1, h437, h469, h473, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h475 | h475
                          · linarith only [h1, h316, h437, h439, h469, h475, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h477 | h477
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h478 | h478
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h479 | h479
                                · linarith only [h437, h439, h463, h469, h479, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h481 | h481
                                  · linarith only [h316, h437, h479, h481, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                                  · rcases h0bigk with h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [hlam, p483_0]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      rcases p483_3 (m.d 0 1) (by simp) with h485 | h485
                                      · rcases p483_3 (m.d 0 2) (by simp) with h486 | h486
                                        · linarith only [h0, h486, hlam]
                                        · rcases p483_3 (m.d 0 3) (by simp) with h488 | h488
                                          · linarith only [h1, h488, hlam]
                                          · linarith only [h4, h488, hlam]
                                      · linarith only [h0, h485, hlam]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [h438, hlam, hphi, ht0b, ht5b, p483_1, u0elo0, u5ehi0]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [h437, h463, h469, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p483_1, u0elo0]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [hlam, hphi, ht0b, ht5b, p483_1, u0elo0, u5ehi0]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [h0, hlam, p483_0]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [hlam, p483_0]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [h4, hlam, p483_0]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [h316, hlam, p483_1]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [h413, hlam, p483_0]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [h1, hlam, p483_1]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      rcases p483_3 (m.d 0 1) (by simp) with h501 | h501
                                      · rcases p483_3 (m.d 0 2) (by simp) with h502 | h502
                                        · linarith only [h4, h502, hlam]
                                        · rcases p483_3 (m.d 0 3) (by simp) with h504 | h504
                                          · rcases p483_3 (m.d 0 4) (by simp) with h505 | h505
                                            · linarith only [h437, h505, hlam]
                                            · linarith only [h316, h505, hlam]
                                          · linarith only [h4, h504, hlam]
                                      · linarith only [h0, h501, hlam]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [hlam, p483_0]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [h437, h463, h469, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p483_1, u0elo2]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [h1, h437, h439, h463, h469, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p483_1, u0elo0]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [h2, hlam, p483_0]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [h0, h316, h479, hc12, hc45, hlam, hphi, ht23, ht34, p483_1]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [h437, hlam, p483_0]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [hlam, p483_0]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [h439, hlam, p483_0]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [h3, hlam, p483_0]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      rcases p483_3 (m.d 0 1) (by simp) with h519 | h519
                                      · rcases p483_3 (m.d 0 2) (by simp) with h520 | h520
                                        · linarith only [h413, h520, hlam]
                                        · rcases p483_3 (m.d 0 3) (by simp) with h522 | h522
                                          · rcases p483_3 (m.d 0 4) (by simp) with h523 | h523
                                            · linarith only [h439, h523, hlam]
                                            · linarith only [h316, h523, hlam]
                                          · linarith only [h4, h522, hlam]
                                      · linarith only [h0, h519, hlam]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [h438, hlam, p483_0]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [h437, h463, h469, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p483_1, u0elo4]
                                    · have p483_0 := h483c.1
                                      have p483_1 := h483c.2.1
                                      have p483_2 := h483c.2.2.1
                                      have p483_3 := h483c.2.2.2
                                      linarith only [hlam, p483_0]
                              · linarith only [h4, h437, h463, h469, h478, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h4, h437, h477, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h533 | h533
              · linarith only [h437, h438, h533, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h535 | h535
                · linarith only [h0, h4, h437, h535, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h537 | h537
                  · linarith only [h0, h316, h537, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h539 | h539
                    · linarith only [h0, h413, h539, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h541 | h541
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h542 | h542
                        · linarith only [h1, h438, h542, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h544 | h544
                          · linarith only [h2, h544, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h546 | h546
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h547 | h547
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h548 | h548
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h549 | h549
                                  · linarith only [h1, h438, h533, h541, h547, h549, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · rcases h0bigk with h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [hlam, p551_0]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      rcases p551_3 (m.d 0 1) (by simp) with h553 | h553
                                      · rcases p551_3 (m.d 0 2) (by simp) with h554 | h554
                                        · linarith only [h0, h554, hlam]
                                        · rcases p551_3 (m.d 0 3) (by simp) with h556 | h556
                                          · linarith only [h1, h556, hlam]
                                          · linarith only [h4, h556, hlam]
                                      · linarith only [h0, h553, hlam]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h1, h541, hc34, hlam, hphi, ht0b, ht45, ht5b, p551_1, u0elo0]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      rcases p551_3 (m.d 0 1) (by simp) with h561 | h561
                                      · rcases p551_3 (m.d 0 2) (by simp) with h562 | h562
                                        · linarith only [h0, h562, hlam]
                                        · rcases p551_3 (m.d 0 3) (by simp) with h564 | h564
                                          · linarith only [h1, h564, hlam]
                                          · linarith only [h437, h564, hlam]
                                      · linarith only [h2, h561, hlam]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h1, h438, h541, hc34, hlam, hphi, ht0b, ht45, ht5b, p551_1, u0elo0]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h0, hlam, p551_0]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [hlam, p551_0]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h4, hlam, p551_0]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h316, hlam, p551_1]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h413, hlam, p551_0]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h1, hlam, p551_1]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h0, h438, h546, h548, h549, hc12, hc23, hlam, hphi, p551_1]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [hlam, p551_0]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h0, h316, h438, h546, h548, h549, hc12, hc23, hlam, hphi, p551_1]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h438, hlam, p551_1]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h2, hlam, p551_0]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h0, h437, h438, h546, h548, h549, hc12, hc23, hlam, hphi, p551_1]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h437, hlam, p551_0]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [hlam, p551_0]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h533, hlam, p551_0]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h3, hlam, p551_0]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h0, h438, h546, h548, h549, hc12, hc23, hlam, hphi, p551_1]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h1, h438, h541, h546, h548, h549, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p551_1]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [h2, h438, h537, h546, h548, h549, hc12, hc23, hlam, hphi, p551_1]
                                    · have p551_0 := h551c.1
                                      have p551_1 := h551c.2.1
                                      have p551_2 := h551c.2.2.1
                                      have p551_3 := h551c.2.2.2
                                      linarith only [hlam, p551_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h589 | h589
                                  · linarith only [h1, h541, h548, h589, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                  · rcases h0bigk with h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [hlam, p591_0]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      rcases p591_3 (m.d 0 1) (by simp) with h593 | h593
                                      · rcases p591_3 (m.d 0 2) (by simp) with h594 | h594
                                        · linarith only [h0, h594, hlam]
                                        · rcases p591_3 (m.d 0 3) (by simp) with h596 | h596
                                          · linarith only [h1, h596, hlam]
                                          · linarith only [h4, h596, hlam]
                                      · linarith only [h0, h593, hlam]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [h1, h541, hc34, hlam, hphi, ht0b, ht45, ht5b, p591_1, u0elo0]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      rcases p591_3 (m.d 0 1) (by simp) with h601 | h601
                                      · rcases p591_3 (m.d 0 2) (by simp) with h602 | h602
                                        · linarith only [h0, h602, hlam]
                                        · rcases p591_3 (m.d 0 3) (by simp) with h604 | h604
                                          · linarith only [h1, h604, hlam]
                                          · linarith only [h437, h604, hlam]
                                      · linarith only [h2, h601, hlam]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [hlam, hphi, ht0b, ht5b, p591_1, u0elo0, u5ehi0]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [h0, hlam, p591_0]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [hlam, p591_0]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [h4, hlam, p591_0]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [h316, hlam, p591_1]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [h413, hlam, p591_0]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [h1, hlam, p591_1]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [h0, h438, h547, hc12, hc25, hlam, hphi, p591_1]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [hlam, p591_0]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [h2, h438, h537, h547, hc12, hc25, hlam, hphi, p591_1]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [h438, hlam, p591_1]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [h2, hlam, p591_0]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [h0, h316, h548, hc12, hc45, hlam, hphi, ht23, ht34, p591_1]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [h437, hlam, p591_0]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [hlam, p591_0]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [h533, hlam, p591_0]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [h3, hlam, p591_0]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [h0, h438, h547, hc12, hc23, hlam, hphi, p591_1]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [h1, h438, h541, h547, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p591_1]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [h0, h316, h438, h547, hc12, hc23, hlam, hphi, p591_1]
                                    · have p591_0 := h591c.1
                                      have p591_1 := h591c.2.1
                                      have p591_2 := h591c.2.2.1
                                      have p591_3 := h591c.2.2.2
                                      linarith only [hlam, p591_0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h629 | h629
                                · linarith only [h0, h316, h533, h546, h547, h629, hc12, hc35, hlam, hphi, ht23]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h631 | h631
                                  · linarith only [h0, h1, h316, h541, h629, h631, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                                  · rcases h0bigk with h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      rcases p633_3 (m.d 0 1) (by simp) with h635 | h635
                                      · rcases p633_3 (m.d 0 2) (by simp) with h636 | h636
                                        · linarith only [h0, h636, hlam]
                                        · rcases p633_3 (m.d 0 3) (by simp) with h638 | h638
                                          · linarith only [h1, h638, hlam]
                                          · linarith only [h4, h638, hlam]
                                      · linarith only [h0, h635, hlam]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h437, hc34, hlam, hphi, ht0b, ht45, ht5b, p633_1, u0elo0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      rcases p633_3 (m.d 0 1) (by simp) with h643 | h643
                                      · rcases p633_3 (m.d 0 2) (by simp) with h644 | h644
                                        · linarith only [h0, h644, hlam]
                                        · rcases p633_3 (m.d 0 3) (by simp) with h646 | h646
                                          · linarith only [h1, h646, hlam]
                                          · linarith only [h437, h646, hlam]
                                      · linarith only [h2, h643, hlam]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [hlam, hphi, ht0b, ht5b, p633_1, u0elo0, u5ehi0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h0, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h4, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h316, hlam, p633_1]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h413, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h1, hlam, p633_1]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h0, h4, h547, h631, hc12, hc45, hlam, hphi, ht23, ht34, p633_1]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h0, h316, h4, h547, h631, hc12, hc45, hlam, hphi, ht23, ht34, p633_1]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h438, hlam, p633_1]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h2, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h0, h4, h437, h547, h631, hc12, hc45, hlam, hphi, ht23, ht34, p633_1]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h437, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h533, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h3, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      rcases p633_3 (m.d 0 1) (by simp) with h667 | h667
                                      · rcases p633_3 (m.d 0 2) (by simp) with h668 | h668
                                        · linarith only [h413, h668, hlam]
                                        · rcases p633_3 (m.d 0 3) (by simp) with h670 | h670
                                          · linarith only [h438, h670, hlam]
                                          · linarith only [h4, h670, hlam]
                                      · linarith only [h0, h667, hlam]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h3, h437, hc34, hlam, hphi, ht0b, ht45, ht5b, p633_1, u0elo0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      rcases p633_3 (m.d 0 1) (by simp) with h675 | h675
                                      · rcases p633_3 (m.d 0 2) (by simp) with h676 | h676
                                        · linarith only [h413, h676, hlam]
                                        · rcases p633_3 (m.d 0 3) (by simp) with h678 | h678
                                          · linarith only [h438, h678, hlam]
                                          · linarith only [h437, h678, hlam]
                                      · linarith only [h2, h675, hlam]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [hlam, p633_0]
                            · linarith only [h1, h541, h546, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h437, h438, h535, h541, hc12, hc35, hlam, hphi, ht23]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h685 | h685
            · rcases m.htr 0 4 5 (by decide) (by decide) with h686 | h686
              · rcases m.htr 1 2 3 (by decide) (by decide) with h687 | h687
                · linarith only [h0, h4, h685, h687, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h689 | h689
                  · linarith only [h0, h316, h689, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h691 | h691
                    · linarith only [h0, h413, h691, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h693 | h693
                      · linarith only [h437, h685, h693, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h695 | h695
                        · linarith only [h2, h693, h695, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h437, h685, h687, h695, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h437, h685, h686, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h699 | h699
              · rcases m.htr 1 2 3 (by decide) (by decide) with h700 | h700
                · linarith only [h0, h4, h700, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h702 | h702
                  · linarith only [h0, h316, h702, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h704 | h704
                    · linarith only [h0, h413, h704, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h706 | h706
                      · linarith only [h1, h4, h437, h706, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h708 | h708
                        · linarith only [h1, h685, h708, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h710 | h710
                          · linarith only [h2, h710, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h712 | h712
                            · linarith only [h437, h699, h700, h706, h710, h712, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h714 | h714
                              · linarith only [h0, h4, h685, h712, h714, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h716 | h716
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h717 | h717
                                  · rcases h0bigk with h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [hlam, p718_0]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      rcases p718_3 (m.d 0 1) (by simp) with h720 | h720
                                      · rcases p718_3 (m.d 0 2) (by simp) with h721 | h721
                                        · linarith only [h0, h721, hlam]
                                        · rcases p718_3 (m.d 0 3) (by simp) with h723 | h723
                                          · linarith only [h1, h723, hlam]
                                          · linarith only [h4, h723, hlam]
                                      · linarith only [h0, h720, hlam]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      rcases p718_3 (m.d 0 1) (by simp) with h727 | h727
                                      · rcases p718_3 (m.d 0 2) (by simp) with h728 | h728
                                        · linarith only [h0, h728, hlam]
                                        · rcases p718_3 (m.d 0 3) (by simp) with h730 | h730
                                          · linarith only [h1, h730, hlam]
                                          · rcases p718_3 (m.d 0 4) (by simp) with h732 | h732
                                            · linarith only [h2, h732, hlam]
                                            · linarith only [h437, h732, hlam]
                                      · linarith only [h1, h727, hlam]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [h699, h700, h706, h710, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p718_1, u0elo0]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [h699, h700, h706, h710, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p718_1, u0elo0]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [h0, hlam, p718_0]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [hlam, p718_0]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [h4, hlam, p718_0]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [h316, hlam, p718_1]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [h413, hlam, p718_0]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [h1, hlam, p718_1]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [h0, h4, h714, h717, hc12, hc34, hlam, hphi, ht23, p718_1]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [hlam, p718_0]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [h437, hlam, p718_1]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [h685, hlam, p718_1]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [h2, hlam, p718_0]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      rcases p718_3 (m.d 0 1) (by simp) with h749 | h749
                                      · rcases p718_3 (m.d 0 2) (by simp) with h750 | h750
                                        · linarith only [h316, h750, hlam]
                                        · rcases p718_3 (m.d 0 3) (by simp) with h752 | h752
                                          · linarith only [h437, h752, hlam]
                                          · linarith only [h4, h752, hlam]
                                      · linarith only [h0, h749, hlam]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      rcases p718_3 (m.d 0 1) (by simp) with h756 | h756
                                      · rcases p718_3 (m.d 0 2) (by simp) with h757 | h757
                                        · linarith only [h316, h757, hlam]
                                        · rcases p718_3 (m.d 0 3) (by simp) with h759 | h759
                                          · linarith only [h437, h759, hlam]
                                          · rcases p718_3 (m.d 0 4) (by simp) with h761 | h761
                                            · rcases p718_3 (m.d 0 5) (by simp) with h762 | h762
                                              · linarith only [h699, h762, hlam]
                                              · linarith only [h685, h762, hlam]
                                            · linarith only [h437, h761, hlam]
                                      · linarith only [h1, h756, hlam]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [hlam, p718_0]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [h2, h699, h700, h706, h710, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p718_1, u0elo0]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [h3, hlam, p718_0]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      rcases p718_3 (m.d 0 1) (by simp) with h770 | h770
                                      · rcases p718_3 (m.d 0 2) (by simp) with h771 | h771
                                        · linarith only [h413, h771, hlam]
                                        · rcases p718_3 (m.d 0 3) (by simp) with h773 | h773
                                          · linarith only [h685, h773, hlam]
                                          · linarith only [h4, h773, hlam]
                                      · linarith only [h0, h770, hlam]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      rcases p718_3 (m.d 0 1) (by simp) with h777 | h777
                                      · rcases p718_3 (m.d 0 2) (by simp) with h778 | h778
                                        · linarith only [h413, h778, hlam]
                                        · rcases p718_3 (m.d 0 3) (by simp) with h780 | h780
                                          · linarith only [h685, h780, hlam]
                                          · rcases p718_3 (m.d 0 4) (by simp) with h782 | h782
                                            · rcases p718_3 (m.d 0 5) (by simp) with h783 | h783
                                              · rcases h2bigk with h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [hlam, p784_0]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [h4, h714, h717, hc12, hc34, hlam, hphi, ht23, p784_1]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [h4, hlam, p784_0]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [h316, hlam, p784_0]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [h413, hlam, p784_0]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [h0, hlam, p784_0]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [hlam, p784_0]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [h700, hlam, p784_0]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [h702, hlam, p784_0]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [h704, hlam, p784_0]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [h714, h717, hc02, hc34, hlam, hphi, ht23, p784_1]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [h714, h717, hc12, hc34, hlam, hphi, ht23, p784_1]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [hlam, p784_0]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [h712, hlam, p784_0]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [h714, hlam, p784_0]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  rcases p784_3 (m.d 0 2) (by simp) with h800 | h800
                                                  · linarith only [h800, hlam, p784_0]
                                                  · rcases p784_3 (m.d 1 2) (by simp) with h802 | h802
                                                    · linarith only [h702, h802, hlam]
                                                    · rcases p784_3 (m.d 2 3) (by simp) with h804 | h804
                                                      · linarith only [h712, h804, hlam]
                                                      · linarith only [h4, h804, hlam]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  rcases p784_3 (m.d 0 2) (by simp) with h807 | h807
                                                  · linarith only [h316, h807, hlam]
                                                  · linarith only [h0, h807, hlam]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [h0, h4, hc12, hc24, hlam, hphi, p784_1]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [hlam, p784_0]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [h1, h413, h700, h712, hc12, hc34, hlam, hphi, ht23, p718_1, p784_1]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  rcases p784_3 (m.d 0 2) (by simp) with h813 | h813
                                                  · linarith only [h813, hlam, p784_0]
                                                  · rcases p784_3 (m.d 1 2) (by simp) with h815 | h815
                                                    · linarith only [h704, h815, hlam]
                                                    · rcases p784_3 (m.d 2 3) (by simp) with h817 | h817
                                                      · linarith only [h714, h817, hlam]
                                                      · linarith only [h4, h817, hlam]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  rcases p784_3 (m.d 0 2) (by simp) with h820 | h820
                                                  · linarith only [h413, h820, hlam]
                                                  · linarith only [h0, h820, hlam]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [h0, h4, hc12, hc25, hlam, hphi, p784_1]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [h716, hlam, p784_0]
                                                · have p784_0 := h784c.1
                                                  have p784_1 := h784c.2.1
                                                  have p784_2 := h784c.2.2.1
                                                  have p784_3 := h784c.2.2.2
                                                  linarith only [hlam, p784_0]
                                              · linarith only [h685, h783, hlam]
                                            · linarith only [h437, h782, hlam]
                                      · linarith only [h1, h777, hlam]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [h699, hlam, p718_1]
                                    · have p718_0 := h718c.1
                                      have p718_1 := h718c.2.1
                                      have p718_2 := h718c.2.2.1
                                      have p718_3 := h718c.2.2.2
                                      linarith only [hlam, p718_0]
                                  · linarith only [h316, h699, h712, h717, hlam]
                                · linarith only [h316, h699, h716, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h833 | h833
                · linarith only [h0, h4, h833, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h835 | h835
                  · linarith only [h0, h316, h835, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h837 | h837
                    · linarith only [h0, h413, h837, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h839 | h839
                      · linarith only [h1, h4, h437, h839, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h841 | h841
                        · linarith only [h1, h841, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h843 | h843
                          · linarith only [h2, h843, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h845 | h845
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h846 | h846
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h847 | h847
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h848 | h848
                                  · linarith only [h0, h4, h437, h699, h845, h848, hc12, hc23, hlam, hphi]
                                  · linarith only [h0, h4, h437, h845, h847, h848, hc12, hc23, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h851 | h851
                                  · linarith only [h0, h316, h847, h851, hc12, hc34, hlam, hphi, ht23]
                                  · rcases h0bigk with h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [hlam, p853_0]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      rcases p853_3 (m.d 0 1) (by simp) with h855 | h855
                                      · rcases p853_3 (m.d 0 2) (by simp) with h856 | h856
                                        · linarith only [h0, h856, hlam]
                                        · rcases p853_3 (m.d 0 3) (by simp) with h858 | h858
                                          · linarith only [h1, h858, hlam]
                                          · linarith only [h4, h858, hlam]
                                      · linarith only [h0, h855, hlam]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      rcases p853_3 (m.d 0 1) (by simp) with h862 | h862
                                      · rcases p853_3 (m.d 0 2) (by simp) with h863 | h863
                                        · linarith only [h0, h863, hlam]
                                        · rcases p853_3 (m.d 0 3) (by simp) with h865 | h865
                                          · linarith only [h1, h865, hlam]
                                          · rcases p853_3 (m.d 0 4) (by simp) with h867 | h867
                                            · linarith only [h2, h867, hlam]
                                            · linarith only [h437, h867, hlam]
                                      · linarith only [h1, h862, hlam]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      rcases p853_3 (m.d 0 1) (by simp) with h871 | h871
                                      · rcases p853_3 (m.d 0 2) (by simp) with h872 | h872
                                        · linarith only [h0, h872, hlam]
                                        · rcases p853_3 (m.d 0 3) (by simp) with h874 | h874
                                          · linarith only [h1, h874, hlam]
                                          · rcases p853_3 (m.d 0 4) (by simp) with h876 | h876
                                            · linarith only [h2, h876, hlam]
                                            · rcases p853_3 (m.d 0 5) (by simp) with h878 | h878
                                              · linarith only [h3, h878, hlam]
                                              · linarith only [h699, h878, hlam]
                                      · linarith only [h2, h871, hlam]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [hlam, hphi, ht0b, ht5b, p853_1, u0elo0, u5ehi0]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [h0, hlam, p853_0]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [hlam, p853_0]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [h4, hlam, p853_0]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [h316, hlam, p853_1]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [h413, hlam, p853_0]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [h1, hlam, p853_1]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [h0, h316, h437, h847, hc12, hc45, hlam, hphi, ht23, ht34, p853_1]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [hlam, p853_0]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [h437, hlam, p853_1]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [h685, hlam, p853_1]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [h2, hlam, p853_0]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [h0, h316, h847, hc12, hc45, hlam, hphi, ht23, ht34, p853_1]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [h316, h847, hc03, hc45, hlam, hphi, ht34, p853_1]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [hlam, p853_0]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [h699, hlam, p853_0]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [h3, hlam, p853_0]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [h0, h685, h846, hc12, hc23, hlam, hphi, p853_1]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [h0, h4, h685, h846, hc12, hc23, hlam, hphi, p853_1]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [h0, h4, h437, h685, h846, hc12, hc23, hlam, hphi, p853_1]
                                    · have p853_0 := h853c.1
                                      have p853_1 := h853c.2.1
                                      have p853_2 := h853c.2.2.1
                                      have p853_3 := h853c.2.2.2
                                      linarith only [hlam, p853_0]
                              · linarith only [h0, h4, h437, h845, h846, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h904 | h904
                              · linarith only [h0, h4, h685, h845, h904, hc12, hc34, hlam, hphi, ht23]
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
                                      rcases p908_3 (m.d 0 1) (by simp) with h910 | h910
                                      · rcases p908_3 (m.d 0 2) (by simp) with h911 | h911
                                        · linarith only [h0, h911, hlam]
                                        · rcases p908_3 (m.d 0 3) (by simp) with h913 | h913
                                          · linarith only [h1, h913, hlam]
                                          · linarith only [h4, h913, hlam]
                                      · linarith only [h0, h910, hlam]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      rcases p908_3 (m.d 0 1) (by simp) with h917 | h917
                                      · rcases p908_3 (m.d 0 2) (by simp) with h918 | h918
                                        · linarith only [h0, h918, hlam]
                                        · rcases p908_3 (m.d 0 3) (by simp) with h920 | h920
                                          · linarith only [h1, h920, hlam]
                                          · rcases p908_3 (m.d 0 4) (by simp) with h922 | h922
                                            · linarith only [h2, h922, hlam]
                                            · linarith only [h437, h922, hlam]
                                      · linarith only [h1, h917, hlam]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      rcases p908_3 (m.d 0 1) (by simp) with h926 | h926
                                      · rcases p908_3 (m.d 0 2) (by simp) with h927 | h927
                                        · linarith only [h0, h927, hlam]
                                        · rcases p908_3 (m.d 0 3) (by simp) with h929 | h929
                                          · linarith only [h1, h929, hlam]
                                          · rcases p908_3 (m.d 0 4) (by simp) with h931 | h931
                                            · linarith only [h2, h931, hlam]
                                            · rcases p908_3 (m.d 0 5) (by simp) with h933 | h933
                                              · linarith only [h3, h933, hlam]
                                              · linarith only [h699, h933, hlam]
                                      · linarith only [h2, h926, hlam]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [hlam, hphi, ht0b, ht5b, p908_1, u0elo0, u5ehi0]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h0, hlam, p908_0]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [hlam, p908_0]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h4, hlam, p908_0]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h316, hlam, p908_1]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h413, hlam, p908_0]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h1, hlam, p908_1]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h0, h437, h699, h906, hc12, hc24, hlam, hphi, p908_1]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [hlam, p908_0]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h437, hlam, p908_1]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h685, hlam, p908_1]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h2, hlam, p908_0]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h0, h699, h906, hc12, hc24, hlam, hphi, p908_1]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h699, h906, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p908_1]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [hlam, p908_0]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h699, hlam, p908_0]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h3, hlam, p908_0]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h0, h699, h906, hc12, hc24, hlam, hphi, p908_1]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h1, h699, h833, h906, hc12, hc24, hlam, hphi, p908_1]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [h0, h316, h699, h906, hc12, hc24, hlam, hphi, p908_1]
                                    · have p908_0 := h908c.1
                                      have p908_1 := h908c.2.1
                                      have p908_2 := h908c.2.2.1
                                      have p908_3 := h908c.2.2.2
                                      linarith only [hlam, p908_0]
                                  · linarith only [h845, h906, h907, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h959 | h959
                                  · linarith only [h0, h4, h845, h906, h959, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h4, h845, h959, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h962 | h962
    · rcases m.htr 0 2 4 (by decide) (by decide) with h963 | h963
      · rcases m.htr 0 2 5 (by decide) (by decide) with h964 | h964
        · linarith only [h0, h3, h964, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h966 | h966
          · rcases m.htr 0 3 5 (by decide) (by decide) with h967 | h967
            · linarith only [h1, h3, h967, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h969 | h969
              · linarith only [h2, h3, h969, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h971 | h971
                · rcases m.htr 1 2 4 (by decide) (by decide) with h972 | h972
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h973 | h973
                    · linarith only [h0, h3, h964, h973, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h975 | h975
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h976 | h976
                        · linarith only [h1, h3, h973, h976, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h0, h3, h971, h976, hc23, hc35, hlam, hphi]
                      · linarith only [h966, h967, h975, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h963, h971, h972, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h962, h964, h971, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h982 | h982
            · linarith only [h1, h3, h982, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h984 | h984
              · linarith only [h0, h3, h963, h984, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h986 | h986
                · rcases m.htr 1 2 4 (by decide) (by decide) with h987 | h987
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h988 | h988
                    · linarith only [h0, h964, h988, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h990 | h990
                      · linarith only [h1, h966, h990, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h992 | h992
                        · linarith only [h1, h3, h982, h988, h992, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                        · linarith only [h0, h3, h986, h992, hc23, hc35, hlam, hphi]
                  · linarith only [h963, h986, h987, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h962, h964, h986, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h997 | h997
        · linarith only [h2, h3, h963, h997, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h999 | h999
          · linarith only [h962, h963, h999, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1001 | h1001
            · linarith only [h0, h1001, h3, h962, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1003 | h1003
              · linarith only [h1003, h2, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1005 | h1005
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1006 | h1006
                  · linarith only [h0, h1006, h963, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1008 | h1008
                    · linarith only [h0, h1008, h3, h997, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1010 | h1010
                      · linarith only [h1, h1008, h1010, h3, h963, h999, hc02, hc25, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1012 | h1012
                        · linarith only [h0, h1, h1001, h1005, h1012, h3, h962, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h1005, h1006, h1012, h2, h3, hc23, hc35, hlam, hphi]
                · linarith only [h1003, h1005, h962, h963, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1016 | h1016
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1017 | h1017
        · linarith only [h0, h1017, h3, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1019 | h1019
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1020 | h1020
            · linarith only [h1, h1020, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1022 | h1022
              · linarith only [h1, h1016, h1022, h3, h962, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1024 | h1024
                · linarith only [h0, h1024, h962, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1026 | h1026
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1027 | h1027
                    · linarith only [h1, h1017, h1024, h1027, h3, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1029 | h1029
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1030 | h1030
                        · linarith only [h1, h1020, h1030, h3, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1032 | h1032
                          · linarith only [h1, h1022, h1024, h1026, h1032, h2, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h1, h1024, h1026, h1032, h3, hc24, hc45, hlam, hphi]
                      · linarith only [h1019, h1024, h1026, h1029, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h1016, h1026, h962, hc12, hc23, hlam, hphi]
          · linarith only [h1016, h1019, h962, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1038 | h1038
        · linarith only [h1, h1038, h3, h962, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1040 | h1040
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1041 | h1041
            · linarith only [h1, h1041, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1043 | h1043
              · linarith only [h1, h1040, h1043, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1045 | h1045
                · linarith only [h0, h1045, h962, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1047 | h1047
                  · linarith only [h0, h1016, h1047, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1049 | h1049
                    · linarith only [h0, h1038, h1049, h3, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1051 | h1051
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1052 | h1052
                        · linarith only [h1, h1052, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1054 | h1054
                          · linarith only [h1, h1016, h1043, h1051, h1052, h1054, h3, hc02, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h1051, h1054, h3, hc34, hc45, hlam, hphi]
                      · linarith only [h1040, h1041, h1051, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1058 | h1058
            · linarith only [h1040, h1058, h2, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1060 | h1060
              · linarith only [h1060, h2, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1062 | h1062
                · linarith only [h0, h1062, h962, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1064 | h1064
                  · linarith only [h0, h1016, h1064, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1066 | h1066
                    · linarith only [h0, h1066, h3, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1068 | h1068
                      · linarith only [h1, h1040, h1068, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1070 | h1070
                        · linarith only [h1, h1058, h1066, h1070, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1072 | h1072
                          · linarith only [h1040, h1060, h1070, h1072, h2, h3, h962, hc02, hc35, hlam, hphi, ht23]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1074 | h1074
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1075 | h1075
                              · linarith only [h0, h1070, h1075, h3, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h1040, h1074, h1075, h962, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1078 | h1078
                              · linarith only [h1062, h1068, h1070, h1078, h2, h3, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1080 | h1080
                                · linarith only [h1062, h1068, h1072, h1080, h2, h3, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1082 | h1082
                                  · linarith only [h0, h1074, h1080, h1082, h962, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h1074, h1082, h962, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
