import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6072000 in
set_option maxHeartbeats 6072000 in
theorem r1l7_20_12_14_M_LI_L_0_L_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
      · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                      · linarith only [h0, h10, h15, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h12, h15, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                      · linarith only [h0, h10, h18, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h12, h18, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h12, h13, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h12, h22, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h24 | h24
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                      · linarith only [h12, h25, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h27 | h27
                        · linarith only [h0, h11, h27, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h2, h24, h27, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                      · linarith only [h0, h10, h30, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h32 | h32
                        · linarith only [h12, h24, h32, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h34 | h34
                          · linarith only [h10, h12, h24, h34, h4, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · linarith only [h10, h12, h34, h4, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h11, h5, hc12, hlam, hphi, u2elo0]
            · linarith only [h10, h4, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
            · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
              · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
                · rcases m.htr 1 3 5 (by decide) (by decide) with h42 | h42
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h43 | h43
                    · linarith only [h2, h43, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
                      · linarith only [h0, h39, h45, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1, h41, h45, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h4, h41, h42, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                  · linarith only [h4, h41, h49, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h51 | h51
                    · linarith only [h2, h51, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h53 | h53
                      · linarith only [h4, h41, h53, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h55 | h55
                        · linarith only [h39, h41, h55, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h57 | h57
                          · linarith only [h57, h7, h9, hlam]
                          · rcases h0bigk with h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h6, hc25, hlam, hphi, ht0b, ht5b, p59_1, u0elo0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h39, h41, h57, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1, u0elo0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h39, h41, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1, u0elo0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h39, h41, h57, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1, u0elo0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h0, hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h39, h41, h57, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1, u0elo1]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h39, h41, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p59_1, u2elo0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h39, h41, h57, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p59_1, u2elo0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h1, hlam, p59_1]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h4, hlam, p59_1]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h39, h41, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1, u0elo2]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h39, h4, h41, h57, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p59_1, u2elo0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h2, hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h5, hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h7, hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h9, hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h3, hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h6, hlam, p59_1]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h8, hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h39, h41, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1, u0elo4]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [hlam, p59_0]
              · linarith only [h40, h5, hc12, hlam, hphi, u2elo0]
            · linarith only [h39, h4, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h87 | h87
          · linarith only [h7, h8, h87, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h89 | h89
            · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
              · rcases m.htr 1 3 4 (by decide) (by decide) with h91 | h91
                · rcases m.htr 1 3 5 (by decide) (by decide) with h92 | h92
                  · linarith only [h1, h8, h92, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
                    · linarith only [h2, h87, h94, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                      · linarith only [h0, h89, h96, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1, h8, h91, h96, hc23, hc35, hlam, hphi]
                · linarith only [h7, h8, h91, hc13, hc35, hlam, hphi]
              · linarith only [h5, h90, hc12, hlam, hphi, u2elo0]
            · linarith only [h4, h89, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h102 | h102
        · rcases m.htr 0 4 5 (by decide) (by decide) with h103 | h103
          · rcases m.htr 1 2 3 (by decide) (by decide) with h104 | h104
            · rcases m.htr 1 2 4 (by decide) (by decide) with h105 | h105
              · rcases m.htr 1 3 4 (by decide) (by decide) with h106 | h106
                · linarith only [h1, h106, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h108 | h108
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h109 | h109
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h110 | h110
                      · linarith only [h1, h104, h108, h110, h7, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h112 | h112
                        · linarith only [h0, h105, h112, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h0, h105, h109, h110, h112, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h103, h106, h108, h109, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                  · linarith only [h102, h108, h7, hc13, hc34, hlam, hphi]
              · linarith only [h105, h5, hc12, hlam, hphi, u2elo0]
            · linarith only [h104, h4, hc12, hlam, hphi, u2elo0]
          · linarith only [h102, h103, h7, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h120 | h120
          · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
            · rcases m.htr 1 2 4 (by decide) (by decide) with h122 | h122
              · rcases m.htr 1 3 4 (by decide) (by decide) with h123 | h123
                · linarith only [h1, h123, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h125 | h125
                  · linarith only [h1, h102, h125, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h127 | h127
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h128 | h128
                      · linarith only [h128, h4, h7, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h130 | h130
                        · linarith only [h0, h122, h130, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h127, h130, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h133 | h133
                      · linarith only [h120, h121, h123, h127, h133, h7, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h135 | h135
                        · linarith only [h121, h123, h127, h135, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h137 | h137
                          · rcases h0bigk with h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [hlam, p138_0]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p138_1, u0elo0]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              rcases p138_3 (m.d 0 1) (by simp) with h141 | h141
                              · rcases p138_3 (m.d 0 2) (by simp) with h142 | h142
                                · linarith only [h0, h142, hlam]
                                · linarith only [h142, h4, hlam]
                              · linarith only [h1, h141, hlam]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [h120, h121, h123, h127, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p138_1, u0elo0]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [h120, h121, h123, h127, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p138_1, u0elo0]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [h0, hlam, p138_0]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [hlam, p138_0]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              rcases p138_3 (m.d 0 1) (by simp) with h150 | h150
                              · rcases p138_3 (m.d 0 2) (by simp) with h151 | h151
                                · rcases p138_3 (m.d 0 3) (by simp) with h152 | h152
                                  · linarith only [h152, h4, hlam]
                                  · rcases p138_3 (m.d 0 4) (by simp) with h154 | h154
                                    · linarith only [h154, h5, hlam]
                                    · linarith only [h154, h7, hlam]
                                · linarith only [h151, h4, hlam]
                              · linarith only [h1, h150, hlam]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [h120, h121, h123, h127, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p138_1, u0elo1]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [h120, h121, h123, h127, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p138_1, u2elo0]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [h1, hlam, p138_1]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [h4, hlam, p138_1]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [hlam, p138_0]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [h7, hlam, p138_1]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [h102, hlam, p138_1]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [h2, hlam, p138_0]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [h5, hlam, p138_0]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              rcases p138_3 (m.d 0 1) (by simp) with h168 | h168
                              · rcases p138_3 (m.d 0 2) (by simp) with h169 | h169
                                · rcases p138_3 (m.d 0 3) (by simp) with h170 | h170
                                  · linarith only [h170, h7, hlam]
                                  · rcases p138_3 (m.d 0 4) (by simp) with h172 | h172
                                    · rcases p138_3 (m.d 0 5) (by simp) with h173 | h173
                                      · linarith only [h120, h173, hlam]
                                      · linarith only [h102, h173, hlam]
                                    · linarith only [h172, h7, hlam]
                                · linarith only [h169, h4, hlam]
                              · linarith only [h1, h168, hlam]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [hlam, p138_0]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [h120, h121, h123, h127, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p138_1, u0elo3]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [h3, hlam, p138_0]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [h6, hlam, p138_1]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              rcases p138_3 (m.d 0 1) (by simp) with h183 | h183
                              · rcases p138_3 (m.d 0 2) (by simp) with h184 | h184
                                · rcases p138_3 (m.d 0 3) (by simp) with h185 | h185
                                  · linarith only [h102, h185, hlam]
                                  · rcases p138_3 (m.d 0 4) (by simp) with h187 | h187
                                    · rcases p138_3 (m.d 0 5) (by simp) with h188 | h188
                                      · rcases h4bigk with h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [hlam, p189_0]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          rcases p189_3 (m.d 0 4) (by simp) with h191 | h191
                                          · rcases p189_3 (m.d 1 4) (by simp) with h192 | h192
                                            · linarith only [h192, h2, hlam]
                                            · rcases p189_3 (m.d 2 4) (by simp) with h194 | h194
                                              · linarith only [h194, h5, hlam]
                                              · rcases p189_3 (m.d 3 4) (by simp) with h196 | h196
                                                · rcases p189_3 (m.d 4 5) (by simp) with h197 | h197
                                                  · linarith only [h120, h197, hlam]
                                                  · linarith only [h127, h197, hlam]
                                                · linarith only [h123, h196, hlam]
                                          · linarith only [h191, h2, hlam]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          rcases p189_3 (m.d 0 4) (by simp) with h202 | h202
                                          · rcases p189_3 (m.d 1 4) (by simp) with h203 | h203
                                            · linarith only [h2, h203, hlam]
                                            · linarith only [h122, h203, hlam]
                                          · linarith only [h202, h5, hlam]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [h7, hlam, p189_0]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [h121, h123, h127, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p189_1, u2elo0]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [h2, hlam, p189_1]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [hlam, p189_0]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [h127, hc24, hc45, hlam, hphi, p189_1]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [h123, hlam, p189_1]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [h127, hlam, p189_0]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [h5, hlam, p189_1]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [h122, hlam, p189_1]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [hlam, p189_0]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [h133, hlam, p189_1]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [h135, hlam, p189_0]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [h1, h120, h121, hc23, hc34, hlam, hphi, p138_1, p189_1]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          rcases p189_3 (m.d 0 4) (by simp) with h220 | h220
                                          · linarith only [h220, h7, hlam]
                                          · linarith only [h2, h220, hlam]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          rcases p189_3 (m.d 0 4) (by simp) with h223 | h223
                                          · linarith only [h223, h7, hlam]
                                          · linarith only [h223, h5, hlam]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [hlam, p189_0]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [h122, h127, h133, hc23, hc34, hlam, hphi, p189_1]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [h120, hlam, p189_0]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [h120, hc14, hlam, hphi, ht0b, ht45, ht5b, p189_1, u0elo3]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [h120, h133, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p189_1, u2elo0]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [h137, hlam, p189_0]
                                        · have p189_0 := h189c.1
                                          have p189_1 := h189c.2.1
                                          have p189_2 := h189c.2.2.1
                                          have p189_3 := h189c.2.2.2
                                          linarith only [hlam, p189_0]
                                      · linarith only [h102, h188, hlam]
                                    · linarith only [h187, h7, hlam]
                                · linarith only [h184, h4, hlam]
                              · linarith only [h1, h183, hlam]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [h120, hlam, p138_1]
                            · have p138_0 := h138c.1
                              have p138_1 := h138c.2.1
                              have p138_2 := h138c.2.2.1
                              have p138_3 := h138c.2.2.2
                              linarith only [hlam, p138_0]
                          · linarith only [h1, h120, h121, h137, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h122, h5, hc12, hlam, hphi, u2elo0]
            · linarith only [h121, h4, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h242 | h242
            · rcases m.htr 1 2 4 (by decide) (by decide) with h243 | h243
              · rcases m.htr 1 3 4 (by decide) (by decide) with h244 | h244
                · linarith only [h1, h244, h7, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h246 | h246
                  · linarith only [h0, h102, h243, h244, h246, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h248 | h248
                    · linarith only [h120, h2, h248, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h250 | h250
                      · linarith only [h1, h242, h250, h7, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h252 | h252
                        · linarith only [h120, h252, h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h254 | h254
                          · rcases h0bigk with h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [hlam, p255_0]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [h0, h243, hc24, hlam, hphi, ht0b, ht45, ht5b, p255_1, u0elo0]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              rcases p255_3 (m.d 0 1) (by simp) with h258 | h258
                              · rcases p255_3 (m.d 0 2) (by simp) with h259 | h259
                                · linarith only [h0, h259, hlam]
                                · linarith only [h259, h4, hlam]
                              · linarith only [h1, h258, hlam]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              rcases p255_3 (m.d 0 1) (by simp) with h263 | h263
                              · rcases p255_3 (m.d 0 2) (by simp) with h264 | h264
                                · linarith only [h0, h264, hlam]
                                · linarith only [h264, h5, hlam]
                              · linarith only [h2, h263, hlam]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              rcases p255_3 (m.d 0 1) (by simp) with h268 | h268
                              · rcases p255_3 (m.d 0 2) (by simp) with h269 | h269
                                · linarith only [h0, h269, hlam]
                                · linarith only [h269, h6, hlam]
                              · linarith only [h268, h3, hlam]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [h0, hlam, p255_0]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [hlam, p255_0]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              rcases p255_3 (m.d 0 1) (by simp) with h275 | h275
                              · rcases p255_3 (m.d 0 2) (by simp) with h276 | h276
                                · rcases p255_3 (m.d 0 3) (by simp) with h277 | h277
                                  · linarith only [h277, h4, hlam]
                                  · rcases p255_3 (m.d 0 4) (by simp) with h279 | h279
                                    · linarith only [h279, h5, hlam]
                                    · linarith only [h279, h7, hlam]
                                · linarith only [h276, h4, hlam]
                              · linarith only [h1, h275, hlam]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              rcases p255_3 (m.d 0 1) (by simp) with h284 | h284
                              · rcases p255_3 (m.d 0 2) (by simp) with h285 | h285
                                · rcases p255_3 (m.d 0 3) (by simp) with h286 | h286
                                  · linarith only [h286, h4, hlam]
                                  · rcases p255_3 (m.d 0 4) (by simp) with h288 | h288
                                    · linarith only [h288, h5, hlam]
                                    · rcases p255_3 (m.d 0 5) (by simp) with h290 | h290
                                      · linarith only [h290, h6, hlam]
                                      · linarith only [h120, h290, hlam]
                                · linarith only [h285, h5, hlam]
                              · linarith only [h2, h284, hlam]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              rcases p255_3 (m.d 0 1) (by simp) with h295 | h295
                              · rcases p255_3 (m.d 0 2) (by simp) with h296 | h296
                                · rcases p255_3 (m.d 0 3) (by simp) with h297 | h297
                                  · linarith only [h297, h4, hlam]
                                  · rcases p255_3 (m.d 0 4) (by simp) with h299 | h299
                                    · linarith only [h299, h5, hlam]
                                    · rcases p255_3 (m.d 0 5) (by simp) with h301 | h301
                                      · linarith only [h301, h6, hlam]
                                      · rcases h4bigk with h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [hlam, p303_0]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [h120, h242, h244, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p255_1, p303_1, u0elo1]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [h120, h250, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p255_1, p303_1, u2elo0]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [h7, hlam, p303_0]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [h120, hlam, p303_0]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [h2, hlam, p303_1]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [hlam, p303_0]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [h2, h250, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p303_1, u0elo0]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [h244, hlam, p303_1]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [h248, hlam, p303_0]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [h5, hlam, p303_1]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [h243, hlam, p303_1]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [hlam, p303_0]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [h250, hlam, p303_1]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [h252, hlam, p303_0]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          rcases p303_3 (m.d 0 4) (by simp) with h319 | h319
                                          · linarith only [h319, h7, hlam]
                                          · rcases p303_3 (m.d 1 4) (by simp) with h321 | h321
                                            · linarith only [h244, h321, hlam]
                                            · rcases p303_3 (m.d 2 4) (by simp) with h323 | h323
                                              · linarith only [h250, h323, hlam]
                                              · rcases p303_3 (m.d 3 4) (by simp) with h325 | h325
                                                · rcases p303_3 (m.d 4 5) (by simp) with h326 | h326
                                                  · linarith only [h254, h326, hlam]
                                                  · linarith only [h120, h326, hlam]
                                                · linarith only [h325, h7, hlam]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          rcases p303_3 (m.d 0 4) (by simp) with h330 | h330
                                          · linarith only [h330, h7, hlam]
                                          · linarith only [h2, h330, hlam]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          rcases p303_3 (m.d 0 4) (by simp) with h333 | h333
                                          · linarith only [h333, h7, hlam]
                                          · linarith only [h333, h5, hlam]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [hlam, p303_0]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [h120, h250, h5, hc23, hc34, hlam, hphi, p303_1]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [h1, h242, h254, h7, hc23, hc34, hlam, hphi, p303_1]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [h243, h250, h254, hc23, hc34, hlam, hphi, p303_1]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [h250, h254, hc23, hc34, hlam, hphi, p303_1]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [h254, hlam, p303_0]
                                        · have p303_0 := h303c.1
                                          have p303_1 := h303c.2.1
                                          have p303_2 := h303c.2.2.1
                                          have p303_3 := h303c.2.2.2
                                          linarith only [hlam, p303_0]
                                · linarith only [h296, h6, hlam]
                              · linarith only [h295, h3, hlam]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [h1, hlam, p255_1]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [h4, hlam, p255_1]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [hlam, p255_0]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [h7, hlam, p255_1]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [h102, hlam, p255_1]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [h2, hlam, p255_0]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [h5, hlam, p255_0]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [h1, h120, h242, h254, hc23, hc34, hlam, hphi, p255_1]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [hlam, p255_0]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [h120, hlam, p255_0]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [h3, hlam, p255_0]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [h6, hlam, p255_1]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [h1, h120, h242, h254, hc23, hc34, hlam, hphi, p255_1]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [h120, h2, h243, h250, h254, hc23, hc34, hlam, hphi, p255_1]
                            · have p255_0 := h255c.1
                              have p255_1 := h255c.2.1
                              have p255_2 := h255c.2.2.1
                              have p255_3 := h255c.2.2.2
                              linarith only [hlam, p255_0]
                          · rcases h0bigk with h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h6, hc25, hlam, hphi, ht0b, ht5b, p360_1, u0elo0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              rcases p360_3 (m.d 0 1) (by simp) with h363 | h363
                              · rcases p360_3 (m.d 0 2) (by simp) with h364 | h364
                                · linarith only [h0, h364, hlam]
                                · linarith only [h364, h4, hlam]
                              · linarith only [h1, h363, hlam]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              rcases p360_3 (m.d 0 1) (by simp) with h368 | h368
                              · rcases p360_3 (m.d 0 2) (by simp) with h369 | h369
                                · linarith only [h0, h369, hlam]
                                · linarith only [h369, h5, hlam]
                              · linarith only [h2, h368, hlam]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              rcases p360_3 (m.d 0 1) (by simp) with h373 | h373
                              · rcases p360_3 (m.d 0 2) (by simp) with h374 | h374
                                · linarith only [h0, h374, hlam]
                                · linarith only [h374, h6, hlam]
                              · linarith only [h3, h373, hlam]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h0, hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              rcases p360_3 (m.d 0 1) (by simp) with h380 | h380
                              · rcases p360_3 (m.d 0 2) (by simp) with h381 | h381
                                · rcases p360_3 (m.d 0 3) (by simp) with h382 | h382
                                  · linarith only [h382, h4, hlam]
                                  · rcases p360_3 (m.d 0 4) (by simp) with h384 | h384
                                    · linarith only [h384, h5, hlam]
                                    · linarith only [h384, h7, hlam]
                                · linarith only [h381, h4, hlam]
                              · linarith only [h1, h380, hlam]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              rcases p360_3 (m.d 0 1) (by simp) with h389 | h389
                              · rcases p360_3 (m.d 0 2) (by simp) with h390 | h390
                                · rcases p360_3 (m.d 0 3) (by simp) with h391 | h391
                                  · linarith only [h391, h4, hlam]
                                  · rcases p360_3 (m.d 0 4) (by simp) with h393 | h393
                                    · linarith only [h393, h5, hlam]
                                    · rcases p360_3 (m.d 0 5) (by simp) with h395 | h395
                                      · linarith only [h395, h6, hlam]
                                      · linarith only [h120, h395, hlam]
                                · linarith only [h390, h5, hlam]
                              · linarith only [h2, h389, hlam]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              rcases p360_3 (m.d 0 1) (by simp) with h400 | h400
                              · rcases p360_3 (m.d 0 2) (by simp) with h401 | h401
                                · rcases p360_3 (m.d 0 3) (by simp) with h402 | h402
                                  · linarith only [h4, h402, hlam]
                                  · rcases p360_3 (m.d 0 4) (by simp) with h404 | h404
                                    · linarith only [h404, h5, hlam]
                                    · rcases p360_3 (m.d 0 5) (by simp) with h406 | h406
                                      · linarith only [h406, h6, hlam]
                                      · rcases h4bigk with h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [hlam, p408_0]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [h243, h250, h254, h7, hc23, hc45, hlam, hphi, ht34, p408_1]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [h250, h254, h7, hc23, hc45, hlam, hphi, ht34, p408_1]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [h7, hlam, p408_0]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [h120, hlam, p408_0]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [h2, hlam, p408_1]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [hlam, p408_0]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [h248, h250, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p360_1, p408_1, u0elo1]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [h244, hlam, p408_1]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [h248, hlam, p408_0]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [h5, hlam, p408_1]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [h243, hlam, p408_1]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [hlam, p408_0]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [h250, hlam, p408_1]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [h252, hlam, p408_0]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [h254, hc04, hc45, hlam, hphi, p408_1]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [h243, h250, h254, hc23, hc45, hlam, hphi, ht34, p408_1]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [h250, h254, hc23, hc45, hlam, hphi, ht34, p408_1]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [hlam, p408_0]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [h254, hlam, p408_0]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          rcases p408_3 (m.d 0 4) (by simp) with h429 | h429
                                          · linarith only [h429, hlam, p408_0]
                                          · rcases p408_3 (m.d 1 4) (by simp) with h431 | h431
                                            · linarith only [h248, h431, hlam]
                                            · rcases p408_3 (m.d 2 4) (by simp) with h433 | h433
                                              · linarith only [h252, h433, hlam]
                                              · rcases p408_3 (m.d 3 4) (by simp) with h435 | h435
                                                · linarith only [h254, h435, hlam]
                                                · linarith only [h435, h7, hlam]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          rcases p408_3 (m.d 0 4) (by simp) with h438 | h438
                                          · linarith only [h120, h438, hlam]
                                          · linarith only [h2, h438, hlam]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          rcases p408_3 (m.d 0 4) (by simp) with h441 | h441
                                          · linarith only [h120, h441, hlam]
                                          · linarith only [h441, h5, hlam]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [h1, h242, h7, hc23, hc45, hlam, hphi, ht34, p408_1]
                                        · have p408_0 := h408c.1
                                          have p408_1 := h408c.2.1
                                          have p408_2 := h408c.2.2.1
                                          have p408_3 := h408c.2.2.2
                                          linarith only [hlam, p408_0]
                                · linarith only [h401, h6, hlam]
                              · linarith only [h3, h400, hlam]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h1, hlam, p360_1]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h4, hlam, p360_1]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h7, hlam, p360_1]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h102, hlam, p360_1]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h2, hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h5, hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h1, h120, h242, hc23, hc45, hlam, hphi, ht34, p360_1]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h120, hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h3, hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h6, hlam, p360_1]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              rcases p360_3 (m.d 0 1) (by simp) with h460 | h460
                              · rcases p360_3 (m.d 0 2) (by simp) with h461 | h461
                                · rcases p360_3 (m.d 0 3) (by simp) with h462 | h462
                                  · linarith only [h102, h462, hlam]
                                  · rcases p360_3 (m.d 0 4) (by simp) with h464 | h464
                                    · linarith only [h120, h464, hlam]
                                    · linarith only [h464, h7, hlam]
                                · linarith only [h4, h461, hlam]
                              · linarith only [h1, h460, hlam]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              rcases p360_3 (m.d 0 1) (by simp) with h469 | h469
                              · rcases p360_3 (m.d 0 2) (by simp) with h470 | h470
                                · rcases p360_3 (m.d 0 3) (by simp) with h471 | h471
                                  · linarith only [h102, h471, hlam]
                                  · rcases p360_3 (m.d 0 4) (by simp) with h473 | h473
                                    · linarith only [h120, h473, hlam]
                                    · rcases p360_3 (m.d 0 5) (by simp) with h475 | h475
                                      · rcases h4bigk with h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c | h476c
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h243, h250, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p360_1, p476_1, u0elo4]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h250, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p360_1, p476_1, u0elo0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h7, hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h120, hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h2, hlam, p476_1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h2, h250, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p476_1, u0elo0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h244, hlam, p476_1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h248, hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h5, hlam, p476_1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h243, hlam, p476_1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h250, hlam, p476_1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h252, hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h254, hc04, hc45, hlam, hphi, p476_1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h243, h250, h254, hc23, hc45, hlam, hphi, ht34, p476_1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h250, h254, hc23, hc45, hlam, hphi, ht34, p476_1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h254, hlam, p476_0]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          rcases p476_3 (m.d 0 4) (by simp) with h497 | h497
                                          · linarith only [h497, hlam, p476_0]
                                          · rcases p476_3 (m.d 1 4) (by simp) with h499 | h499
                                            · linarith only [h248, h499, hlam]
                                            · rcases p476_3 (m.d 2 4) (by simp) with h501 | h501
                                              · linarith only [h252, h501, hlam]
                                              · rcases p476_3 (m.d 3 4) (by simp) with h503 | h503
                                                · linarith only [h254, h503, hlam]
                                                · linarith only [h503, h7, hlam]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          rcases p476_3 (m.d 0 4) (by simp) with h506 | h506
                                          · linarith only [h120, h506, hlam]
                                          · linarith only [h2, h506, hlam]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          rcases p476_3 (m.d 0 4) (by simp) with h509 | h509
                                          · linarith only [h120, h509, hlam]
                                          · linarith only [h5, h509, hlam]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [h1, h242, h7, hc23, hc45, hlam, hphi, ht34, p476_1]
                                        · have p476_0 := h476c.1
                                          have p476_1 := h476c.2.1
                                          have p476_2 := h476c.2.2.1
                                          have p476_3 := h476c.2.2.2
                                          linarith only [hlam, p476_0]
                                      · linarith only [h120, h475, hlam]
                                · linarith only [h470, h5, hlam]
                              · linarith only [h2, h469, hlam]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [hlam, p360_0]
              · linarith only [h243, h5, hc12, hlam, hphi, u2elo0]
            · linarith only [h242, h4, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h520 | h520
      · rcases m.htr 0 3 5 (by decide) (by decide) with h521 | h521
        · linarith only [h4, h521, h6, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h523 | h523
          · linarith only [h4, h520, h523, h6, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h525 | h525
            · rcases m.htr 1 2 4 (by decide) (by decide) with h526 | h526
              · rcases m.htr 1 3 4 (by decide) (by decide) with h527 | h527
                · rcases m.htr 1 3 5 (by decide) (by decide) with h528 | h528
                  · linarith only [h1, h521, h528, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h530 | h530
                    · linarith only [h2, h523, h530, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h532 | h532
                      · linarith only [h0, h525, h532, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h4, h520, h532, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h4, h520, h527, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h5, h526, h6, hc12, hlam, hphi, u2elo4]
            · linarith only [h4, h525, h6, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h538 | h538
        · linarith only [h5, h520, h538, h6, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h540 | h540
          · linarith only [h5, h540, h6, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h542 | h542
            · rcases m.htr 1 2 4 (by decide) (by decide) with h543 | h543
              · rcases m.htr 1 3 4 (by decide) (by decide) with h544 | h544
                · linarith only [h1, h520, h544, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h546 | h546
                  · linarith only [h0, h1, h538, h542, h546, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h548 | h548
                    · linarith only [h2, h540, h548, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h550 | h550
                      · linarith only [h4, h520, h550, h6, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h552 | h552
                        · linarith only [h0, h540, h543, h552, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h554 | h554
                          · linarith only [h0, h543, h550, h552, h554, h6, hc23, hc34, hlam, hphi]
                          · rcases h0bigk with h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [hlam, p556_0]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [h0, h543, h550, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p556_1, u0elo0]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              rcases p556_3 (m.d 0 1) (by simp) with h559 | h559
                              · rcases p556_3 (m.d 0 2) (by simp) with h560 | h560
                                · linarith only [h0, h560, hlam]
                                · linarith only [h4, h560, hlam]
                              · linarith only [h1, h559, hlam]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              rcases p556_3 (m.d 0 1) (by simp) with h564 | h564
                              · rcases p556_3 (m.d 0 2) (by simp) with h565 | h565
                                · linarith only [h0, h565, hlam]
                                · linarith only [h5, h565, hlam]
                              · linarith only [h2, h564, hlam]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [h0, h543, h550, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p556_1, u0elo0]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [h0, hlam, p556_0]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [hlam, p556_0]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [h1, h542, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p556_1, u2elo4]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [h1, h520, h542, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p556_1, u2elo4]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [h6, hlam, p556_0]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [h1, hlam, p556_1]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [h4, hlam, p556_1]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [hlam, p556_0]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [h520, hlam, p556_1]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [h538, hlam, p556_1]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [h2, hlam, p556_0]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [h5, hlam, p556_0]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [h1, h5, h542, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p556_1, u2elo4]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [hlam, p556_0]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [h540, hlam, p556_0]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [h3, hlam, p556_0]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [h0, h543, h550, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p556_1, u0elo4]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              rcases p556_3 (m.d 0 1) (by simp) with h587 | h587
                              · rcases p556_3 (m.d 0 2) (by simp) with h588 | h588
                                · linarith only [h588, h6, hlam]
                                · linarith only [h4, h588, hlam]
                              · linarith only [h1, h587, hlam]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              rcases p556_3 (m.d 0 1) (by simp) with h592 | h592
                              · rcases p556_3 (m.d 0 2) (by simp) with h593 | h593
                                · linarith only [h593, h6, hlam]
                                · linarith only [h5, h593, hlam]
                              · linarith only [h2, h592, hlam]
                            · have p556_0 := h556c.1
                              have p556_1 := h556c.2.1
                              have p556_2 := h556c.2.2.1
                              have p556_3 := h556c.2.2.2
                              linarith only [hlam, p556_0]
              · linarith only [h5, h543, hc12, hlam, hphi, u2elo0]
            · linarith only [h4, h542, h6, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h600 | h600
    · rcases m.htr 0 3 4 (by decide) (by decide) with h601 | h601
      · linarith only [h4, h5, h601, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h603 | h603
        · rcases m.htr 0 4 5 (by decide) (by decide) with h604 | h604
          · rcases m.htr 1 2 3 (by decide) (by decide) with h605 | h605
            · rcases m.htr 1 2 4 (by decide) (by decide) with h606 | h606
              · linarith only [h5, h606, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h608 | h608
                · linarith only [h1, h601, h608, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h610 | h610
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h611 | h611
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h612 | h612
                      · linarith only [h0, h1, h601, h605, h610, h612, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h614 | h614
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h615 | h615
                          · rcases h0bigk with h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [hlam, p616_0]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h0, h605, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p616_1, u0elo0]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h1, h610, h615, hc45, hlam, hphi, ht0b, ht5b, p616_1, u0elo0]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h2, h605, h606, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p616_1, u0elo0]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              rcases p616_3 (m.d 0 1) (by simp) with h621 | h621
                              · rcases p616_3 (m.d 0 2) (by simp) with h622 | h622
                                · linarith only [h0, h622, hlam]
                                · linarith only [h600, h622, hlam]
                              · linarith only [h3, h621, hlam]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h0, hlam, p616_0]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [hlam, p616_0]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h1, h610, h615, hc45, hlam, hphi, ht0b, ht5b, p616_1, u0elo1]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h5, hlam, p616_1]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h5, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p616_1, u2elo3]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h1, hlam, p616_1]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h4, hlam, p616_1]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [hlam, p616_0]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h601, hlam, p616_1]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h3, h4, h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p616_1, u2elo3]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h2, hlam, p616_0]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h0, h605, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p616_1, u0elo3]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h1, h5, h610, h615, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p616_1, u2elo3]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [hlam, p616_0]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              rcases p616_3 (m.d 0 1) (by simp) with h640 | h640
                              · rcases p616_3 (m.d 0 2) (by simp) with h641 | h641
                                · linarith only [h5, h641, hlam]
                                · linarith only [h600, h641, hlam]
                              · linarith only [h3, h640, hlam]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h3, hlam, p616_0]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h600, hlam, p616_1]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h603, hlam, p616_0]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [h604, hlam, p616_1]
                            · have p616_0 := h616c.1
                              have p616_1 := h616c.2.1
                              have p616_2 := h616c.2.2.1
                              have p616_3 := h616c.2.2.2
                              linarith only [hlam, p616_0]
                          · linarith only [h0, h5, h605, h612, h615, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h3, h5, h605, h611, h614, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h4, h5, h603, h604, h605, h606, h611, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h4, h5, h603, h610, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h4, h5, h605, hc12, hlam, hphi, u2elo3]
          · linarith only [h4, h5, h603, h604, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h656 | h656
          · rcases m.htr 1 2 3 (by decide) (by decide) with h657 | h657
            · rcases m.htr 1 2 4 (by decide) (by decide) with h658 | h658
              · linarith only [h5, h658, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h660 | h660
                · linarith only [h1, h601, h660, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h662 | h662
                  · linarith only [h1, h603, h662, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h664 | h664
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h665 | h665
                      · linarith only [h0, h5, h601, h657, h665, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h667 | h667
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h668 | h668
                          · rcases h0bigk with h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [hlam, p669_0]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [h0, h657, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p669_1, u0elo0]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              rcases p669_3 (m.d 0 1) (by simp) with h672 | h672
                              · rcases p669_3 (m.d 0 2) (by simp) with h673 | h673
                                · linarith only [h0, h673, hlam]
                                · linarith only [h4, h673, hlam]
                              · linarith only [h1, h672, hlam]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [h0, h5, h657, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p669_1, u0elo0]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              rcases p669_3 (m.d 0 1) (by simp) with h678 | h678
                              · rcases p669_3 (m.d 0 2) (by simp) with h679 | h679
                                · linarith only [h0, h679, hlam]
                                · linarith only [h600, h679, hlam]
                              · linarith only [h3, h678, hlam]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [h0, hlam, p669_0]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [hlam, p669_0]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [h1, h5, h657, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p669_1, u2elo3]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [h5, hlam, p669_1]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [h5, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p669_1, u2elo3]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [h1, hlam, p669_1]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [h4, hlam, p669_1]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [hlam, p669_0]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [h601, hlam, p669_1]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [h603, hlam, p669_1]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [h2, hlam, p669_0]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [h600, hc25, hlam, hphi, ht0b, ht5b, p669_1, u0elo3]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              rcases p669_3 (m.d 0 1) (by simp) with h695 | h695
                              · rcases p669_3 (m.d 0 2) (by simp) with h696 | h696
                                · linarith only [h5, h696, hlam]
                                · linarith only [h4, h696, hlam]
                              · linarith only [h1, h695, hlam]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [hlam, p669_0]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              rcases p669_3 (m.d 0 1) (by simp) with h701 | h701
                              · rcases p669_3 (m.d 0 2) (by simp) with h702 | h702
                                · linarith only [h5, h702, hlam]
                                · linarith only [h600, h702, hlam]
                              · linarith only [h3, h701, hlam]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [h3, hlam, p669_0]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [h600, hlam, p669_1]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [h1, h5, h600, h657, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p669_1, u2elo3]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [h656, hlam, p669_1]
                            · have p669_0 := h669c.1
                              have p669_1 := h669c.2.1
                              have p669_2 := h669c.2.2.1
                              have p669_3 := h669c.2.2.2
                              linarith only [hlam, p669_0]
                          · linarith only [h5, h665, h667, h668, hc02, hlam, hphi, u2elo4]
                        · linarith only [h0, h5, h657, h667, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h5, h600, h656, h657, h658, h664, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h4, h5, h657, hc12, hlam, hphi, u2elo3]
          · linarith only [h5, h600, h656, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h716 | h716
      · linarith only [h4, h5, h716, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h718 | h718
        · linarith only [h4, h600, h718, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h720 | h720
          · rcases m.htr 1 2 3 (by decide) (by decide) with h721 | h721
            · rcases m.htr 1 2 4 (by decide) (by decide) with h722 | h722
              · linarith only [h5, h722, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h724 | h724
                · linarith only [h0, h5, h716, h721, h724, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h726 | h726
                  · linarith only [h1, h4, h600, h718, h726, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h728 | h728
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h729 | h729
                      · linarith only [h0, h5, h716, h721, h729, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h731 | h731
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h732 | h732
                          · rcases h0bigk with h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [hlam, p733_0]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p733_1, u0elo0]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              rcases p733_3 (m.d 0 1) (by simp) with h736 | h736
                              · rcases p733_3 (m.d 0 2) (by simp) with h737 | h737
                                · linarith only [h0, h737, hlam]
                                · linarith only [h4, h737, hlam]
                              · linarith only [h1, h736, hlam]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [h0, h600, h720, h721, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p733_1, u0elo0]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [h0, h600, h721, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p733_1, u0elo0]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [h0, hlam, p733_0]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [hlam, p733_0]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [h1, h5, h721, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p733_1, u2elo3]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [h5, hlam, p733_1]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [h600, hlam, p733_0]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [h1, hlam, p733_1]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [h4, hlam, p733_1]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [hlam, p733_0]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [h716, hlam, p733_1]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [h718, hlam, p733_1]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [h2, hlam, p733_0]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [h0, h721, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p733_1, u0elo3]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              rcases p733_3 (m.d 0 1) (by simp) with h755 | h755
                              · rcases p733_3 (m.d 0 2) (by simp) with h756 | h756
                                · linarith only [h5, h756, hlam]
                                · linarith only [h4, h756, hlam]
                              · linarith only [h1, h755, hlam]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [hlam, p733_0]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [h0, h5, h600, h721, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p733_1, u2elo3]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [h3, hlam, p733_0]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [h0, h721, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p733_1, u0elo4]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              rcases p733_3 (m.d 0 1) (by simp) with h764 | h764
                              · rcases p733_3 (m.d 0 2) (by simp) with h765 | h765
                                · linarith only [h600, h765, hlam]
                                · linarith only [h4, h765, hlam]
                              · linarith only [h1, h764, hlam]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [h720, hlam, p733_1]
                            · have p733_0 := h733c.1
                              have p733_1 := h733c.2.1
                              have p733_2 := h733c.2.2.1
                              have p733_3 := h733c.2.2.2
                              linarith only [hlam, p733_0]
                          · linarith only [h0, h5, h721, h729, h732, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h2, h5, h721, h728, h731, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h5, h720, h721, h722, h728, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h4, h721, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h775 | h775
            · rcases m.htr 1 2 4 (by decide) (by decide) with h776 | h776
              · linarith only [h0, h5, h776, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h778 | h778
                · linarith only [h1, h2, h716, h775, h776, h778, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h780 | h780
                  · linarith only [h1, h4, h600, h718, h780, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h782 | h782
                    · linarith only [h2, h720, h782, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h784 | h784
                      · linarith only [h0, h600, h716, h775, h784, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h786 | h786
                        · linarith only [h2, h720, h776, h786, hc12, hlam, hphi, u2elo3]
                        · linarith only [h0, h5, h775, h786, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h4, h5, h775, hc12, hlam, hphi, u2elo3]

end R2N4
