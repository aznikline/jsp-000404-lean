import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
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
                        · linarith only [h0, h16, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · linarith only [h15, h16, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                        · linarith only [h0, h12, h15, h19, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                          · linarith only [h0, h10, h21, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
                            · linarith only [h0, h12, h21, h23, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                            · linarith only [h15, h23, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                        · linarith only [h0, h27, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · linarith only [h13, h14, h26, h27, h8, hc34, hlam, hphi, ht45, u5elo0]
                      · linarith only [h12, h14, h26, h8, hc23, hlam, hphi, ht34, ht45, u5elo0]
                  · linarith only [h12, h13, h7, hc34, hlam, hphi, ht45, u5elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
                  · linarith only [h0, h12, h32, h4, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                      · linarith only [h32, h35, h7, h9, hc34, hlam, hphi, ht45, u5elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                        · linarith only [h32, h37, h9, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h39 | h39
                          · linarith only [h0, h10, h39, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h41 | h41
                            · rcases h1bigk with h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h10, h34, h35, h39, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p42_1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                rcases p42_3 (m.d 0 1) (by simp) with h45 | h45
                                · rcases p42_3 (m.d 1 2) (by simp) with h46 | h46
                                  · linarith only [h0, h46, hlam]
                                  · linarith only [h46, h9, hlam]
                                · linarith only [h45, hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h34, h35, h39, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p42_1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                rcases p42_3 (m.d 0 1) (by simp) with h51 | h51
                                · rcases p42_3 (m.d 1 2) (by simp) with h52 | h52
                                  · linarith only [h0, h52, hlam]
                                  · linarith only [h11, h52, hlam]
                                · linarith only [h51, hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h0, hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                rcases p42_3 (m.d 0 1) (by simp) with h58 | h58
                                · rcases p42_3 (m.d 1 2) (by simp) with h59 | h59
                                  · rcases p42_3 (m.d 1 3) (by simp) with h60 | h60
                                    · linarith only [h60, h9, hlam]
                                    · rcases p42_3 (m.d 1 4) (by simp) with h62 | h62
                                      · linarith only [h10, h62, hlam]
                                      · linarith only [h12, h62, hlam]
                                  · linarith only [h59, h9, hlam]
                                · linarith only [h1, h58, hlam]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h34, h35, h39, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42_1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p42_1, u5ehi6]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h1, hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h9, hlam, p42_1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h12, hlam, p42_1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h32, hlam, p42_1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h2, hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h10, hlam, p42_1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                rcases p42_3 (m.d 0 1) (by simp) with h76 | h76
                                · rcases p42_3 (m.d 1 2) (by simp) with h77 | h77
                                  · rcases p42_3 (m.d 1 3) (by simp) with h78 | h78
                                    · linarith only [h12, h78, hlam]
                                    · rcases p42_3 (m.d 1 4) (by simp) with h80 | h80
                                      · rcases p42_3 (m.d 1 5) (by simp) with h81 | h81
                                        · linarith only [h34, h81, hlam]
                                        · linarith only [h32, h81, hlam]
                                      · linarith only [h12, h80, hlam]
                                  · linarith only [h77, h9, hlam]
                                · linarith only [h1, h76, hlam]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h12, h34, h35, h39, hc23, hc34, hlam, hphi, p42_1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h3, hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h11, hlam, p42_1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [hc13, hlam, hphi, ht34, ht45, p42_1, u5elo1]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [h34, hlam, p42_0]
                              · have p42_0 := h42c.1
                                have p42_1 := h42c.2.1
                                have p42_2 := h42c.2.2.1
                                have p42_3 := h42c.2.2.2
                                linarith only [hlam, p42_0]
                            · linarith only [h12, h41, h8, h9, hc23, hlam, hphi, ht34, ht45, u5elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h95 | h95
                      · linarith only [h12, h9, h95, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h97 | h97
                        · linarith only [h0, h12, h32, h4, h6, h9, h97, hc01, hlam, hphi, ht0b, ht5b, u5ehi6]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h99 | h99
                          · linarith only [h0, h10, h12, h34, h99, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h101 | h101
                            · rcases h1bigk with h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [hlam, p102_0]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [h11, hc01, hlam, hphi, ht0b, ht5b, p102_1, u5ehi7]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [h0, h101, h12, h34, h4, h6, hlam, p102_2]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [h0, h101, h34, h4, h6, hlam, p102_2]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                rcases p102_3 (m.d 0 1) (by simp) with h107 | h107
                                · rcases p102_3 (m.d 1 2) (by simp) with h108 | h108
                                  · linarith only [h0, h108, hlam]
                                  · linarith only [h108, h11, hlam]
                                · linarith only [h107, hlam, p102_0]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [h0, hlam, p102_0]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [hlam, p102_0]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                rcases p102_3 (m.d 0 1) (by simp) with h114 | h114
                                · rcases p102_3 (m.d 1 2) (by simp) with h115 | h115
                                  · rcases p102_3 (m.d 1 3) (by simp) with h116 | h116
                                    · linarith only [h116, h9, hlam]
                                    · rcases p102_3 (m.d 1 4) (by simp) with h118 | h118
                                      · linarith only [h10, h118, hlam]
                                      · linarith only [h118, h12, hlam]
                                  · linarith only [h115, h9, hlam]
                                · linarith only [h1, h114, hlam]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                rcases p102_3 (m.d 0 1) (by simp) with h123 | h123
                                · rcases p102_3 (m.d 1 2) (by simp) with h124 | h124
                                  · rcases p102_3 (m.d 1 3) (by simp) with h125 | h125
                                    · linarith only [h125, h9, hlam]
                                    · rcases p102_3 (m.d 1 4) (by simp) with h127 | h127
                                      · linarith only [h10, h127, hlam]
                                      · rcases p102_3 (m.d 1 5) (by simp) with h129 | h129
                                        · linarith only [h11, h129, hlam]
                                        · linarith only [h129, h34, hlam]
                                  · linarith only [h10, h124, hlam]
                                · linarith only [h123, h2, hlam]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [h0, h11, hc01, hlam, hphi, ht0b, ht5b, p102_1, u5ehi7]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [h1, hlam, p102_0]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [h9, hlam, p102_1]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [hlam, p102_0]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [h12, hlam, p102_1]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [h32, hlam, p102_1]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [h2, hlam, p102_0]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [h10, hlam, p102_1]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [h0, h101, h34, h4, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p102_1]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [hlam, p102_0]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [h34, hlam, p102_1]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [h3, hlam, p102_0]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [h11, hlam, p102_1]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [h9, hc23, hlam, hphi, ht34, ht45, p102_1, u5elo1]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [h0, h101, h34, h4, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p102_1]
                              · have p102_0 := h102c.1
                                have p102_1 := h102c.2.1
                                have p102_2 := h102c.2.2.1
                                have p102_3 := h102c.2.2.2
                                linarith only [hlam, p102_0]
                            · linarith only [h101, h12, h8, h9, hc23, hlam, hphi, ht34, ht45, u5elo0]
              · linarith only [h11, h5, h9, hc23, hlam, hphi, ht34, ht45, u5elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h152 | h152
              · rcases m.htr 1 3 4 (by decide) (by decide) with h153 | h153
                · linarith only [h10, h153, h9, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h155 | h155
                  · linarith only [h0, h153, h155, h4, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h157 | h157
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h158 | h158
                      · linarith only [h155, h158, h7, h9, hc34, hlam, hphi, ht45, u5elo0]
                      · linarith only [h0, h10, h152, h158, h4, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                    · linarith only [h10, h152, h157, hlam, hphi, u5ehi7, u5elo4]
              · linarith only [h152, h5, h9, hc23, hlam, hphi, ht34, ht45, u5elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h163 | h163
            · rcases m.htr 1 2 5 (by decide) (by decide) with h164 | h164
              · linarith only [h0, h164, h4, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
              · linarith only [h163, h164, h5, hc24, hlam, hphi, ht45, u5elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h167 | h167
              · linarith only [h0, h167, h4, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h169 | h169
                · rcases m.htr 1 3 5 (by decide) (by decide) with h170 | h170
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h171 | h171
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h173 | h173
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h174 | h174
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h175 | h175
                            · linarith only [h1, h169, h175, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · rcases h1bigk with h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [hlam, p177_0]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                rcases p177_3 (m.d 0 1) (by simp) with h179 | h179
                                · rcases p177_3 (m.d 1 2) (by simp) with h180 | h180
                                  · linarith only [h180, hlam, p177_0]
                                  · rcases p177_3 (m.d 1 3) (by simp) with h182 | h182
                                    · linarith only [h1, h182, hlam]
                                    · linarith only [h182, h9, hlam]
                                · linarith only [h179, hlam, p177_0]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [h169, h171, h175, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p177_1]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [h171, h175, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p177_1]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                rcases p177_3 (m.d 0 1) (by simp) with h188 | h188
                                · rcases p177_3 (m.d 1 2) (by simp) with h189 | h189
                                  · linarith only [h0, h189, hlam]
                                  · rcases p177_3 (m.d 1 3) (by simp) with h191 | h191
                                    · linarith only [h1, h191, hlam]
                                    · linarith only [h170, h191, hlam]
                                · linarith only [h188, hlam, p177_0]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [h0, hlam, p177_0]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [hlam, p177_0]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [h9, hlam, p177_0]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [h163, hlam, p177_0]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [h167, hlam, p177_0]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [h1, hlam, p177_0]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                rcases p177_3 (m.d 0 1) (by simp) with h201 | h201
                                · rcases p177_3 (m.d 1 2) (by simp) with h202 | h202
                                  · linarith only [h202, h9, hlam]
                                  · rcases p177_3 (m.d 1 3) (by simp) with h204 | h204
                                    · rcases p177_3 (m.d 1 4) (by simp) with h205 | h205
                                      · linarith only [h169, h205, hlam]
                                      · linarith only [h163, h205, hlam]
                                    · linarith only [h204, h9, hlam]
                                · linarith only [h0, h201, hlam]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [hlam, p177_0]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [h171, h175, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p177_1]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [h0, h171, h175, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p177_1]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [h2, hlam, p177_0]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                rcases p177_3 (m.d 0 1) (by simp) with h214 | h214
                                · rcases p177_3 (m.d 1 2) (by simp) with h215 | h215
                                  · linarith only [h163, h215, hlam]
                                  · rcases p177_3 (m.d 1 3) (by simp) with h217 | h217
                                    · rcases p177_3 (m.d 1 4) (by simp) with h218 | h218
                                      · rcases p177_3 (m.d 1 5) (by simp) with h219 | h219
                                        · linarith only [h171, h219, hlam]
                                        · linarith only [h167, h219, hlam]
                                      · linarith only [h163, h218, hlam]
                                    · linarith only [h217, h9, hlam]
                                · linarith only [h0, h214, hlam]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [h169, hlam, p177_0]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [hlam, p177_0]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [h171, h175, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p177_1]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [h3, hlam, p177_0]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p177_1, u5elo1]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [h170, hlam, p177_0]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [h171, hlam, p177_0]
                              · have p177_0 := h177c.1
                                have p177_1 := h177c.2.1
                                have p177_2 := h177c.2.2.1
                                have p177_3 := h177c.2.2.2
                                linarith only [hlam, p177_0]
                          · linarith only [h163, h174, h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                        · linarith only [h173, h7, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                      · linarith only [h0, h170, h172, h4, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h236 | h236
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h237 | h237
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h238 | h238
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h239 | h239
                            · linarith only [h169, h171, h239, hlam]
                            · rcases h1bigk with h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [hlam, p241_0]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [h0, h163, h171, h236, h238, h4, hlam, p241_2]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [h170, hc01, hlam, hphi, ht0b, ht5b, p241_1, u5ehi8]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [h0, h171, h236, h238, h4, hlam, p241_2]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                rcases p241_3 (m.d 0 1) (by simp) with h246 | h246
                                · rcases p241_3 (m.d 1 2) (by simp) with h247 | h247
                                  · linarith only [h0, h247, hlam]
                                  · rcases p241_3 (m.d 1 3) (by simp) with h249 | h249
                                    · linarith only [h1, h249, hlam]
                                    · linarith only [h170, h249, hlam]
                                · linarith only [h246, hlam, p241_0]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [h0, hlam, p241_0]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [hlam, p241_0]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [h9, hlam, p241_0]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [h163, hlam, p241_0]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [h167, hlam, p241_0]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [h1, hlam, p241_0]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                rcases p241_3 (m.d 0 1) (by simp) with h259 | h259
                                · rcases p241_3 (m.d 1 2) (by simp) with h260 | h260
                                  · linarith only [h260, h9, hlam]
                                  · rcases p241_3 (m.d 1 3) (by simp) with h262 | h262
                                    · rcases p241_3 (m.d 1 4) (by simp) with h263 | h263
                                      · linarith only [h169, h263, hlam]
                                      · linarith only [h163, h263, hlam]
                                    · linarith only [h262, h9, hlam]
                                · linarith only [h0, h259, hlam]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [hlam, p241_0]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                rcases p241_3 (m.d 0 1) (by simp) with h269 | h269
                                · rcases p241_3 (m.d 1 2) (by simp) with h270 | h270
                                  · linarith only [h270, h9, hlam]
                                  · rcases p241_3 (m.d 1 3) (by simp) with h272 | h272
                                    · rcases p241_3 (m.d 1 4) (by simp) with h273 | h273
                                      · linarith only [h169, h273, hlam]
                                      · rcases p241_3 (m.d 1 5) (by simp) with h275 | h275
                                        · linarith only [h170, h275, hlam]
                                        · linarith only [h171, h275, hlam]
                                    · linarith only [h169, h272, hlam]
                                · linarith only [h2, h269, hlam]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p241_1, u5ehi6]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [h2, hlam, p241_0]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [h0, h171, h236, h238, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p241_1]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [h169, hlam, p241_0]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [hlam, p241_0]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [h171, hlam, p241_1]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [h3, hlam, p241_0]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p241_1, u5elo1]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [h170, hlam, p241_0]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [h0, h171, h236, h238, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p241_1]
                              · have p241_0 := h241c.1
                                have p241_1 := h241c.2.1
                                have p241_2 := h241c.2.2.1
                                have p241_3 := h241c.2.2.2
                                linarith only [hlam, p241_0]
                          · linarith only [h163, h238, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h237, h7, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                      · linarith only [h0, h170, h236, h4, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                  · linarith only [h169, h170, h7, hc34, hlam, hphi, ht45, u5elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h295 | h295
                  · linarith only [h0, h169, h295, h4, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h297 | h297
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h298 | h298
                      · linarith only [h0, h169, h297, h298, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h300 | h300
                        · linarith only [h0, h298, h300, h4, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · linarith only [h300, h7, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h303 | h303
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h304 | h304
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h305 | h305
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h306 | h306
                            · linarith only [h0, h297, h303, h306, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h169, h306, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h163, h305, h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                        · linarith only [h304, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h311 | h311
                        · linarith only [h0, h303, h311, h4, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · linarith only [h311, h7, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h314 | h314
          · rcases m.htr 1 2 4 (by decide) (by decide) with h315 | h315
            · rcases m.htr 1 2 5 (by decide) (by decide) with h316 | h316
              · rcases m.htr 1 3 4 (by decide) (by decide) with h317 | h317
                · rcases m.htr 1 3 5 (by decide) (by decide) with h318 | h318
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h319 | h319
                    · linarith only [h2, h319, h8, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h321 | h321
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h322 | h322
                        · linarith only [h0, h314, h322, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · linarith only [h321, h322, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h321, h6, h8, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h317, h318, h7, h8, hc34, hlam, hphi, ht45, u5elo4]
                · linarith only [h314, h317, h6, h8, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h314, h316, h5, h8, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h2, h314, h315, h8, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h330 | h330
            · rcases m.htr 1 2 5 (by decide) (by decide) with h331 | h331
              · linarith only [h0, h314, h331, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
              · linarith only [h330, h331, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h334 | h334
              · linarith only [h2, h330, h334, h8, hlam, hphi, u5ehi7, u5elo4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h336 | h336
                · rcases m.htr 1 3 5 (by decide) (by decide) with h337 | h337
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h338 | h338
                    · linarith only [h2, h338, h8, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h340 | h340
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h341 | h341
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h342 | h342
                          · linarith only [h342, h5, h8, hlam]
                          · linarith only [h330, h342, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h314, h337, h341, hlam]
                      · linarith only [h314, h337, h340, h6, hc03, hlam, hphi, ht0b, ht5b, u5ehi8]
                  · linarith only [h336, h337, hc34, hlam, hphi, ht45, u5elo3]
                · linarith only [h336, h6, h8, hc13, hlam, hphi, ht34, ht45, u5elo4]
      · linarith only [h6, h7, hc34, hlam, hphi, ht45, u5elo3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h350 | h350
      · rcases m.htr 0 4 5 (by decide) (by decide) with h351 | h351
        · rcases m.htr 1 2 3 (by decide) (by decide) with h352 | h352
          · rcases m.htr 1 2 4 (by decide) (by decide) with h353 | h353
            · rcases m.htr 1 2 5 (by decide) (by decide) with h354 | h354
              · rcases m.htr 1 3 4 (by decide) (by decide) with h355 | h355
                · linarith only [h350, h355, h6, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h357 | h357
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h358 | h358
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h359 | h359
                      · linarith only [h1, h357, h359, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h361 | h361
                        · linarith only [h0, h353, h359, h361, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · linarith only [h1, h357, h361, h6, hc23, hc34, hlam, hphi]
                    · linarith only [h355, h357, h358, hlam, hphi, u5ehi8, u5elo4]
                  · linarith only [h350, h357, h6, hc13, hc34, hlam, hphi]
              · linarith only [h353, h354, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h367 | h367
              · rcases m.htr 1 3 4 (by decide) (by decide) with h368 | h368
                · linarith only [h350, h368, h6, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h370 | h370
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h371 | h371
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h372 | h372
                      · linarith only [h1, h370, h372, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h374 | h374
                        · linarith only [h352, h353, h372, h374, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                        · linarith only [h1, h370, h374, h6, hc23, hc34, hlam, hphi]
                    · linarith only [h351, h352, h353, h370, h371, hc04, hlam, hphi, ht0b, ht5b, u5ehi8]
                  · linarith only [h350, h370, h6, hc13, hc34, hlam, hphi]
              · linarith only [h352, h367, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h380 | h380
            · rcases m.htr 1 2 5 (by decide) (by decide) with h381 | h381
              · linarith only [h352, h381, h4, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
              · linarith only [h380, h381, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h384 | h384
              · linarith only [h352, h384, h4, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h386 | h386
                · linarith only [h350, h386, h6, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h388 | h388
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h389 | h389
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h390 | h390
                      · linarith only [h390, h4, h6, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h392 | h392
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h393 | h393
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h394 | h394
                            · rcases h1bigk with h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [hlam, p395_0]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                rcases p395_3 (m.d 0 1) (by simp) with h397 | h397
                                · rcases p395_3 (m.d 1 2) (by simp) with h398 | h398
                                  · linarith only [h398, hlam, p395_0]
                                  · rcases p395_3 (m.d 1 3) (by simp) with h400 | h400
                                    · linarith only [h1, h400, hlam]
                                    · linarith only [h352, h400, hlam]
                                · linarith only [h397, hlam, p395_0]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [h388, h394, hc01, hlam, hphi, ht0b, ht5b, p395_1, u5ehi9]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [h386, h388, h394, hc01, hlam, hphi, ht0b, ht5b, p395_1, u5ehi9]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                rcases p395_3 (m.d 0 1) (by simp) with h406 | h406
                                · rcases p395_3 (m.d 1 2) (by simp) with h407 | h407
                                  · linarith only [h0, h407, hlam]
                                  · rcases p395_3 (m.d 1 3) (by simp) with h409 | h409
                                    · linarith only [h1, h409, hlam]
                                    · linarith only [h388, h409, hlam]
                                · linarith only [h406, hlam, p395_0]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [h0, hlam, p395_0]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [hlam, p395_0]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [h352, hlam, p395_0]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [h380, hlam, p395_0]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [h384, hlam, p395_0]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [h1, hlam, p395_0]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [h352, h4, h6, hc12, hc34, hlam, hphi, ht23, p395_1]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [hlam, p395_0]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [h386, hlam, p395_1]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [h352, h4, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p395_1, u5ehi6]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [h2, hlam, p395_0]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                rcases p395_3 (m.d 0 1) (by simp) with h424 | h424
                                · rcases p395_3 (m.d 1 2) (by simp) with h425 | h425
                                  · linarith only [h380, h425, hlam]
                                  · rcases p395_3 (m.d 1 3) (by simp) with h427 | h427
                                    · linarith only [h386, h427, hlam]
                                    · linarith only [h352, h427, hlam]
                                · linarith only [h0, h424, hlam]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [h380, h388, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p395_1, u5ehi8]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [hlam, p395_0]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [h2, h388, h394, hc01, hlam, hphi, ht0b, ht5b, p395_1, u5ehi9]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [h3, hlam, p395_0]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [h352, h388, h394, h4, h6, hc12, hc34, hlam, hphi, ht23, p395_1, u5ehi9, u5elo1]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [h388, hlam, p395_0]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [h389, hlam, p395_0]
                              · have p395_0 := h395c.1
                                have p395_1 := h395c.2.1
                                have p395_2 := h395c.2.2.1
                                have p395_3 := h395c.2.2.2
                                linarith only [hlam, p395_0]
                            · linarith only [h352, h388, h394, h4, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                          · linarith only [h380, h389, h393, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
                        · linarith only [h352, h388, h392, hlam]
                    · linarith only [h351, h386, h388, h389, hlam, hphi, u5ehi8, u5elo0]
                  · linarith only [h350, h388, h6, hc13, hc34, hlam, hphi]
        · linarith only [h350, h351, h6, hlam, hphi, u5ehi8, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h445 | h445
        · rcases m.htr 1 2 3 (by decide) (by decide) with h446 | h446
          · rcases m.htr 1 2 4 (by decide) (by decide) with h447 | h447
            · rcases m.htr 1 2 5 (by decide) (by decide) with h448 | h448
              · rcases m.htr 1 3 4 (by decide) (by decide) with h449 | h449
                · linarith only [h1, h449, h6, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h451 | h451
                  · linarith only [h1, h350, h451, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h453 | h453
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h454 | h454
                      · linarith only [h0, h2, h4, h453, h454, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h456 | h456
                        · linarith only [h1, h350, h446, h456, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h458 | h458
                          · linarith only [h0, h447, h458, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h460 | h460
                            · rcases h1bigk with h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [hlam, p461_0]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [h447, h453, h454, h458, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p461_1]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                rcases p461_3 (m.d 0 1) (by simp) with h464 | h464
                                · rcases p461_3 (m.d 1 2) (by simp) with h465 | h465
                                  · linarith only [h0, h465, hlam]
                                  · linarith only [h446, h465, hlam]
                                · linarith only [h464, hlam, p461_0]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [h453, h454, h458, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p461_1]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                rcases p461_3 (m.d 0 1) (by simp) with h470 | h470
                                · rcases p461_3 (m.d 1 2) (by simp) with h471 | h471
                                  · linarith only [h0, h471, hlam]
                                  · linarith only [h448, h471, hlam]
                                · linarith only [h470, hlam, p461_0]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [h0, hlam, p461_0]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [hlam, p461_0]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                rcases p461_3 (m.d 0 1) (by simp) with h477 | h477
                                · rcases p461_3 (m.d 1 2) (by simp) with h478 | h478
                                  · rcases p461_3 (m.d 1 3) (by simp) with h479 | h479
                                    · linarith only [h446, h479, hlam]
                                    · rcases p461_3 (m.d 1 4) (by simp) with h481 | h481
                                      · linarith only [h447, h481, hlam]
                                      · linarith only [h449, h481, hlam]
                                  · linarith only [h446, h478, hlam]
                                · linarith only [h1, h477, hlam]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [h453, h454, h458, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p461_1]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p461_1, u5ehi6]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [h1, hlam, p461_0]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [h446, hlam, p461_1]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [hlam, p461_0]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [h449, hlam, p461_1]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [h451, hlam, p461_1]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [h2, hlam, p461_0]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [h447, hlam, p461_1]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                rcases p461_3 (m.d 0 1) (by simp) with h495 | h495
                                · rcases p461_3 (m.d 1 2) (by simp) with h496 | h496
                                  · rcases p461_3 (m.d 1 3) (by simp) with h497 | h497
                                    · linarith only [h449, h497, hlam]
                                    · rcases p461_3 (m.d 1 4) (by simp) with h499 | h499
                                      · rcases p461_3 (m.d 1 5) (by simp) with h500 | h500
                                        · linarith only [h453, h500, hlam]
                                        · linarith only [h451, h500, hlam]
                                      · linarith only [h449, h499, hlam]
                                  · linarith only [h446, h496, hlam]
                                · linarith only [h1, h495, hlam]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [hlam, p461_0]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [h2, h453, h454, h458, h6, hc23, hc34, hlam, hphi, p461_1]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [h3, hlam, p461_0]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [h448, hlam, p461_1]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [hc13, hlam, hphi, ht34, ht45, p461_1, u5elo1]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [h453, hlam, p461_0]
                              · have p461_0 := h461c.1
                                have p461_1 := h461c.2.1
                                have p461_2 := h461c.2.2.1
                                have p461_3 := h461c.2.2.2
                                linarith only [hlam, p461_0]
                            · linarith only [h460, h6, hc03, hlam, hphi, ht34, ht45, u5elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h514 | h514
                      · linarith only [h445, h446, h449, h453, h514, h6, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h516 | h516
                        · linarith only [h350, h445, h446, h449, h453, h516, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h518 | h518
                          · linarith only [h0, h446, h447, h449, h453, h518, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h520 | h520
                            · rcases h1bigk with h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [hlam, p521_0]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [h448, hc01, hlam, hphi, ht0b, ht5b, p521_1, u5ehi7]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                rcases p521_3 (m.d 0 1) (by simp) with h524 | h524
                                · rcases p521_3 (m.d 1 2) (by simp) with h525 | h525
                                  · linarith only [h0, h525, hlam]
                                  · linarith only [h446, h525, hlam]
                                · linarith only [h524, hlam, p521_0]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                rcases p521_3 (m.d 0 1) (by simp) with h529 | h529
                                · rcases p521_3 (m.d 1 2) (by simp) with h530 | h530
                                  · linarith only [h0, h530, hlam]
                                  · linarith only [h447, h530, hlam]
                                · linarith only [h529, hlam, p521_0]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                rcases p521_3 (m.d 0 1) (by simp) with h534 | h534
                                · rcases p521_3 (m.d 1 2) (by simp) with h535 | h535
                                  · linarith only [h0, h535, hlam]
                                  · linarith only [h448, h535, hlam]
                                · linarith only [h534, hlam, p521_0]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [h0, hlam, p521_0]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [hlam, p521_0]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                rcases p521_3 (m.d 0 1) (by simp) with h541 | h541
                                · rcases p521_3 (m.d 1 2) (by simp) with h542 | h542
                                  · rcases p521_3 (m.d 1 3) (by simp) with h543 | h543
                                    · linarith only [h446, h543, hlam]
                                    · rcases p521_3 (m.d 1 4) (by simp) with h545 | h545
                                      · linarith only [h447, h545, hlam]
                                      · linarith only [h449, h545, hlam]
                                  · linarith only [h446, h542, hlam]
                                · linarith only [h1, h541, hlam]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                rcases p521_3 (m.d 0 1) (by simp) with h550 | h550
                                · rcases p521_3 (m.d 1 2) (by simp) with h551 | h551
                                  · rcases p521_3 (m.d 1 3) (by simp) with h552 | h552
                                    · linarith only [h446, h552, hlam]
                                    · rcases p521_3 (m.d 1 4) (by simp) with h554 | h554
                                      · linarith only [h447, h554, hlam]
                                      · rcases p521_3 (m.d 1 5) (by simp) with h556 | h556
                                        · linarith only [h448, h556, hlam]
                                        · linarith only [h453, h556, hlam]
                                  · linarith only [h447, h551, hlam]
                                · linarith only [h2, h550, hlam]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [h0, h448, hc01, hlam, hphi, ht0b, ht5b, p521_1, u5ehi7]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [h1, hlam, p521_0]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [h446, hlam, p521_1]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [hlam, p521_0]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [h449, hlam, p521_1]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [h451, hlam, p521_1]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [h2, hlam, p521_0]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [h447, hlam, p521_1]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [h445, h446, h453, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p521_1]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [hlam, p521_0]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [h453, hlam, p521_1]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [h3, hlam, p521_0]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [h448, hlam, p521_1]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [h446, hc23, hlam, hphi, ht34, ht45, p521_1, u5elo1]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [h350, h445, h453, hc14, hlam, hphi, ht45, p521_1, u5elo3]
                              · have p521_0 := h521c.1
                                have p521_1 := h521c.2.1
                                have p521_2 := h521c.2.2.1
                                have p521_3 := h521c.2.2.2
                                linarith only [hlam, p521_0]
                            · linarith only [h445, h520, h6, hlam]
              · linarith only [h350, h446, h448, h5, hc23, hlam, hphi, ht34, ht45, u5elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h579 | h579
              · rcases m.htr 1 3 4 (by decide) (by decide) with h580 | h580
                · linarith only [h1, h445, h580, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h582 | h582
                  · linarith only [h1, h350, h582, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h584 | h584
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h585 | h585
                      · linarith only [h350, h4, h585, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h587 | h587
                        · linarith only [h1, h350, h446, h587, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h589 | h589
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h590 | h590
                            · rcases h1bigk with h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h579, h589, hc01, hlam, hphi, ht0b, ht5b, p591_1, u5ehi9]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                rcases p591_3 (m.d 0 1) (by simp) with h594 | h594
                                · rcases p591_3 (m.d 1 2) (by simp) with h595 | h595
                                  · linarith only [h0, h595, hlam]
                                  · linarith only [h446, h595, hlam]
                                · linarith only [h594, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h447, h579, h589, hc01, hlam, hphi, ht0b, ht5b, p591_1, u5ehi9]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                rcases p591_3 (m.d 0 1) (by simp) with h600 | h600
                                · rcases p591_3 (m.d 1 2) (by simp) with h601 | h601
                                  · linarith only [h0, h601, hlam]
                                  · linarith only [h579, h601, hlam]
                                · linarith only [h600, hlam, p591_0]
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
                                linarith only [h447, h585, hc13, hc34, hlam, hphi, p591_1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h447, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h447, h585, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p591_1, u5ehi6]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h1, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h446, hlam, p591_1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h580, hlam, p591_1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h582, hlam, p591_1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h2, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h2, h446, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p591_1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                rcases p591_3 (m.d 0 1) (by simp) with h617 | h617
                                · rcases p591_3 (m.d 1 2) (by simp) with h618 | h618
                                  · linarith only [h447, h618, hlam]
                                  · linarith only [h446, h618, hlam]
                                · linarith only [h1, h617, hlam]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h2, h579, h589, hc01, hlam, hphi, ht0b, ht5b, p591_1, u5ehi9]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h3, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h579, hlam, p591_1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h446, h447, h579, h585, h589, hc23, hc34, hlam, hphi, p591_1, u5ehi9, u5elo1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h584, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [hlam, p591_0]
                            · linarith only [h447, h579, h585, h589, h590, hlam]
                          · linarith only [h447, h579, h589, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi7]
                    · linarith only [h445, h447, h579, h584, hc04, hlam, hphi, ht0b, ht5b, u5ehi7]
              · linarith only [h446, h579, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h350, h4, h446, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h634 | h634
          · rcases m.htr 1 2 4 (by decide) (by decide) with h635 | h635
            · rcases m.htr 1 2 5 (by decide) (by decide) with h636 | h636
              · rcases m.htr 1 3 4 (by decide) (by decide) with h637 | h637
                · linarith only [h1, h445, h6, h637, hc34, hlam, hphi, ht45, u5elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h639 | h639
                  · linarith only [h1, h350, h445, h6, h639, hlam, hphi, u5ehi5, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h641 | h641
                    · linarith only [h2, h445, h641, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h643 | h643
                      · linarith only [h4, h6, h643, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h645 | h645
                        · linarith only [h1, h350, h634, h645, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h647 | h647
                          · linarith only [h2, h445, h635, h647, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h649 | h649
                            · rcases h1bigk with h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [hlam, p650_0]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [h636, hc01, hlam, hphi, ht0b, ht5b, p650_1, u5ehi7]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                rcases p650_3 (m.d 0 1) (by simp) with h653 | h653
                                · rcases p650_3 (m.d 1 2) (by simp) with h654 | h654
                                  · linarith only [h0, h654, hlam]
                                  · linarith only [h634, h654, hlam]
                                · linarith only [h653, hlam, p650_0]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                rcases p650_3 (m.d 0 1) (by simp) with h658 | h658
                                · rcases p650_3 (m.d 1 2) (by simp) with h659 | h659
                                  · linarith only [h0, h659, hlam]
                                  · linarith only [h635, h659, hlam]
                                · linarith only [h658, hlam, p650_0]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                rcases p650_3 (m.d 0 1) (by simp) with h663 | h663
                                · rcases p650_3 (m.d 1 2) (by simp) with h664 | h664
                                  · linarith only [h0, h664, hlam]
                                  · linarith only [h636, h664, hlam]
                                · linarith only [h663, hlam, p650_0]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [h0, hlam, p650_0]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [hlam, p650_0]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                rcases p650_3 (m.d 0 1) (by simp) with h670 | h670
                                · rcases p650_3 (m.d 1 2) (by simp) with h671 | h671
                                  · rcases p650_3 (m.d 1 3) (by simp) with h672 | h672
                                    · linarith only [h634, h672, hlam]
                                    · rcases p650_3 (m.d 1 4) (by simp) with h674 | h674
                                      · linarith only [h635, h674, hlam]
                                      · linarith only [h637, h674, hlam]
                                  · linarith only [h634, h671, hlam]
                                · linarith only [h1, h670, hlam]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                rcases p650_3 (m.d 0 1) (by simp) with h679 | h679
                                · rcases p650_3 (m.d 1 2) (by simp) with h680 | h680
                                  · rcases p650_3 (m.d 1 3) (by simp) with h681 | h681
                                    · linarith only [h634, h681, hlam]
                                    · rcases p650_3 (m.d 1 4) (by simp) with h683 | h683
                                      · linarith only [h635, h683, hlam]
                                      · rcases p650_3 (m.d 1 5) (by simp) with h685 | h685
                                        · linarith only [h636, h685, hlam]
                                        · linarith only [h641, h685, hlam]
                                  · linarith only [h635, h680, hlam]
                                · linarith only [h2, h679, hlam]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [h0, h636, hc01, hlam, hphi, ht0b, ht5b, p650_1, u5ehi7]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [h1, hlam, p650_0]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [h634, hlam, p650_1]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [hlam, p650_0]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [h637, hlam, p650_1]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [h639, hlam, p650_1]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [h2, hlam, p650_0]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [h635, hlam, p650_1]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [h2, h445, h649, hc13, hlam, hphi, ht34, ht45, p650_1, u5elo3]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [hlam, p650_0]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [h641, hlam, p650_1]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [h3, hlam, p650_0]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [h636, hlam, p650_1]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [h3, h634, hc23, hlam, hphi, ht34, ht45, p650_1, u5elo0]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [h3, h445, h649, hc14, hlam, hphi, ht45, p650_1, u5elo3]
                              · have p650_0 := h650c.1
                                have p650_1 := h650c.2.1
                                have p650_2 := h650c.2.2.1
                                have p650_3 := h650c.2.2.2
                                linarith only [hlam, p650_0]
                            · linarith only [h1, h6, h634, h649, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h350, h5, h634, h636, hc23, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h2, h445, h634, h635, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h4, h445, h6, h634, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
  · linarith only [h4, h5, hc23, hlam, hphi, ht34, ht45, u5elo2]

end R2N4
