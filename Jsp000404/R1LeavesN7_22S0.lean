import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
        · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                        · linarith only [h0, h10, h16, h19, hc01, hc45, hlam, hphi, ht0b, ht5b]
                        · linarith only [h19, hc34, hlam, hphi, ht45, u5elo4]
                      · linarith only [h15, h18, h3, hc24, hlam, hphi, ht45, u5elo0]
                    · linarith only [h17, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                    · linarith only [h0, h10, h13, h16, h24, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h24, hc23, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h15, hc14, hlam, hphi, ht45, u5elo4]
              · linarith only [h14, hc13, hlam, hphi, ht34, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 4 5 (by decide) (by decide) with h30 | h30
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                  · linarith only [h0, h13, h29, h31, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h33 | h33
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h34 | h34
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h35 | h35
                        · rcases h0bigk with h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h33, h35, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p36_1]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h10, h13, h33, h35, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p36_1]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h10, h13, h33, h35, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p36_1]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            rcases p36_3 (m.d 0 1) (by simp) with h41 | h41
                            · rcases p36_3 (m.d 0 2) (by simp) with h42 | h42
                              · linarith only [h0, h42, hlam]
                              · linarith only [h42, h6, hlam]
                            · linarith only [h3, h41, hlam]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h0, hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h10, h13, h33, h35, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p36_1]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h0, h10, h13, h33, h35, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p36_1]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            rcases p36_3 (m.d 0 1) (by simp) with h50 | h50
                            · rcases p36_3 (m.d 0 2) (by simp) with h51 | h51
                              · rcases p36_3 (m.d 0 3) (by simp) with h52 | h52
                                · linarith only [h4, h52, hlam]
                                · linarith only [h52, h8, hlam]
                              · linarith only [h51, h6, hlam]
                            · linarith only [h3, h50, hlam]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h1, hlam, p36_1]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h4, hlam, p36_1]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h10, h13, h33, h35, h7, hc03, hc45, hlam, hphi, ht0b, ht5b, p36_1]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            rcases p36_3 (m.d 0 1) (by simp) with h61 | h61
                            · rcases p36_3 (m.d 0 2) (by simp) with h62 | h62
                              · rcases p36_3 (m.d 0 3) (by simp) with h63 | h63
                                · rcases p36_3 (m.d 0 4) (by simp) with h64 | h64
                                  · linarith only [h64, h7, hlam]
                                  · linarith only [h64, h9, hlam]
                                · linarith only [h63, h8, hlam]
                              · linarith only [h6, h62, hlam]
                            · linarith only [h3, h61, hlam]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h2, hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h5, hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h7, hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            rcases p36_3 (m.d 0 1) (by simp) with h74 | h74
                            · rcases p36_3 (m.d 0 2) (by simp) with h75 | h75
                              · rcases p36_3 (m.d 0 3) (by simp) with h76 | h76
                                · rcases p36_3 (m.d 0 4) (by simp) with h77 | h77
                                  · rcases p36_3 (m.d 0 5) (by simp) with h78 | h78
                                    · linarith only [h78, h9, hlam]
                                    · rcases h0emin with h80 | h80 | h80 | h80 | h80
                                      · rcases h2bigk with h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [hlam, p81_0]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [h0, h10, h33, h35, hc01, hc45, hlam, hphi, ht0b, ht5b, p81_1]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          rcases p81_3 (m.d 0 2) (by simp) with h84 | h84
                                          · rcases p81_3 (m.d 1 2) (by simp) with h85 | h85
                                            · linarith only [h0, h85, hlam]
                                            · linarith only [h10, h85, hlam]
                                          · linarith only [h84, hlam, p81_0]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          rcases p81_3 (m.d 0 2) (by simp) with h89 | h89
                                          · rcases p81_3 (m.d 1 2) (by simp) with h90 | h90
                                            · linarith only [h0, h90, hlam]
                                            · linarith only [h11, h90, hlam]
                                          · linarith only [h89, hlam, p81_0]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          rcases p81_3 (m.d 0 2) (by simp) with h94 | h94
                                          · rcases p81_3 (m.d 1 2) (by simp) with h95 | h95
                                            · linarith only [h0, h95, hlam]
                                            · linarith only [h12, h95, hlam]
                                          · linarith only [h94, hlam, p81_0]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [h0, hlam, p81_0]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [hlam, p81_0]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [h0, h33, h35, hc01, hc45, hlam, hphi, ht0b, ht5b, p81_1]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [h0, h31, h33, h35, hc01, hc45, hlam, hphi, ht0b, ht5b, p81_1]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          rcases p81_3 (m.d 0 2) (by simp) with h103 | h103
                                          · rcases p81_3 (m.d 1 2) (by simp) with h104 | h104
                                            · rcases p81_3 (m.d 2 3) (by simp) with h105 | h105
                                              · linarith only [h10, h105, hlam]
                                              · linarith only [h105, h33, hlam]
                                            · linarith only [h104, hlam, p81_0]
                                          · linarith only [h103, h6, hlam]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [h4, hlam, p81_0]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [h10, hlam, p81_0]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [hlam, p81_0]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [h31, hlam, p81_0]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [h10, h13, h4, h7, hc02, hc25, hlam, hphi, ht0b, ht5b, p81_1]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [h5, hlam, p81_0]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [h11, hlam, p81_0]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p81_1]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [hlam, p81_0]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [h0, h11, h33, h35, hc01, hc45, hlam, hphi, ht0b, ht5b, p81_1]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [h6, hlam, p81_0]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [h12, hlam, p81_0]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [h33, hlam, p81_1]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [h34, hlam, p81_0]
                                        · have p81_0 := h81c.1
                                          have p81_1 := h81c.2.1
                                          have p81_2 := h81c.2.2.1
                                          have p81_3 := h81c.2.2.2
                                          linarith only [hlam, p81_0]
                                      · rcases h2bigk with h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, h10, h33, h35, hc01, hc45, hlam, hphi, ht0b, ht5b, p125_1]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          rcases p125_3 (m.d 0 2) (by simp) with h128 | h128
                                          · rcases p125_3 (m.d 1 2) (by simp) with h129 | h129
                                            · linarith only [h0, h129, hlam]
                                            · linarith only [h10, h129, hlam]
                                          · linarith only [h128, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          rcases p125_3 (m.d 0 2) (by simp) with h133 | h133
                                          · rcases p125_3 (m.d 1 2) (by simp) with h134 | h134
                                            · linarith only [h0, h134, hlam]
                                            · linarith only [h11, h134, hlam]
                                          · linarith only [h133, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          rcases p125_3 (m.d 0 2) (by simp) with h138 | h138
                                          · rcases p125_3 (m.d 1 2) (by simp) with h139 | h139
                                            · linarith only [h0, h139, hlam]
                                            · linarith only [h12, h139, hlam]
                                          · linarith only [h138, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, h33, h35, hc01, hc45, hlam, hphi, ht0b, ht5b, p125_1]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, h31, h33, h35, hc01, hc45, hlam, hphi, ht0b, ht5b, p125_1]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          rcases p125_3 (m.d 0 2) (by simp) with h147 | h147
                                          · rcases p125_3 (m.d 1 2) (by simp) with h148 | h148
                                            · rcases p125_3 (m.d 2 3) (by simp) with h149 | h149
                                              · linarith only [h10, h149, hlam]
                                              · linarith only [h149, h33, hlam]
                                            · linarith only [h148, hlam, p125_0]
                                          · linarith only [h147, h6, hlam]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h4, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h10, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h31, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, h10, hc01, hc25, hlam, hphi, ht0b, ht5b, p125_1]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h5, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h11, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p125_1]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, h11, h33, h35, hc01, hc45, hlam, hphi, ht0b, ht5b, p125_1]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h6, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h12, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h33, hlam, p125_1]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h34, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [hlam, p125_0]
                                      · rcases h2bigk with h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h0, h10, h33, h35, hc01, hc45, hlam, hphi, ht0b, ht5b, p169_1]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          rcases p169_3 (m.d 0 2) (by simp) with h172 | h172
                                          · rcases p169_3 (m.d 1 2) (by simp) with h173 | h173
                                            · linarith only [h0, h173, hlam]
                                            · linarith only [h10, h173, hlam]
                                          · linarith only [h172, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          rcases p169_3 (m.d 0 2) (by simp) with h177 | h177
                                          · rcases p169_3 (m.d 1 2) (by simp) with h178 | h178
                                            · linarith only [h0, h178, hlam]
                                            · linarith only [h11, h178, hlam]
                                          · linarith only [h177, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          rcases p169_3 (m.d 0 2) (by simp) with h182 | h182
                                          · rcases p169_3 (m.d 1 2) (by simp) with h183 | h183
                                            · linarith only [h0, h183, hlam]
                                            · linarith only [h12, h183, hlam]
                                          · linarith only [h182, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h0, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h0, h33, h35, hc01, hc45, hlam, hphi, ht0b, ht5b, p169_1]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h0, h31, h33, h35, hc01, hc45, hlam, hphi, ht0b, ht5b, p169_1]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          rcases p169_3 (m.d 0 2) (by simp) with h191 | h191
                                          · rcases p169_3 (m.d 1 2) (by simp) with h192 | h192
                                            · rcases p169_3 (m.d 2 3) (by simp) with h193 | h193
                                              · linarith only [h10, h193, hlam]
                                              · linarith only [h193, h33, hlam]
                                            · linarith only [h192, hlam, p169_0]
                                          · linarith only [h191, h6, hlam]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h4, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h10, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h31, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h0, h10, hc01, hc25, hlam, hphi, ht0b, ht5b, p169_1]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h5, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h11, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p169_1]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h0, h11, h33, h35, hc01, hc45, hlam, hphi, ht0b, ht5b, p169_1]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h6, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h12, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h33, hlam, p169_1]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [h34, hlam, p169_0]
                                        · have p169_0 := h169c.1
                                          have p169_1 := h169c.2.1
                                          have p169_2 := h169c.2.2.1
                                          have p169_3 := h169c.2.2.2
                                          linarith only [hlam, p169_0]
                                      · rcases h2bigk with h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [hlam, p213_0]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [h0, h10, h33, h35, hc01, hc45, hlam, hphi, ht0b, ht5b, p213_1]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          rcases p213_3 (m.d 0 2) (by simp) with h216 | h216
                                          · rcases p213_3 (m.d 1 2) (by simp) with h217 | h217
                                            · linarith only [h0, h217, hlam]
                                            · linarith only [h10, h217, hlam]
                                          · linarith only [h216, hlam, p213_0]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          rcases p213_3 (m.d 0 2) (by simp) with h221 | h221
                                          · rcases p213_3 (m.d 1 2) (by simp) with h222 | h222
                                            · linarith only [h0, h222, hlam]
                                            · linarith only [h11, h222, hlam]
                                          · linarith only [h221, hlam, p213_0]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          rcases p213_3 (m.d 0 2) (by simp) with h226 | h226
                                          · rcases p213_3 (m.d 1 2) (by simp) with h227 | h227
                                            · linarith only [h0, h227, hlam]
                                            · linarith only [h12, h227, hlam]
                                          · linarith only [h226, hlam, p213_0]
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
                                          linarith only [h0, h33, h35, hc01, hc45, hlam, hphi, ht0b, ht5b, p213_1]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [h0, h31, h33, h35, hc01, hc45, hlam, hphi, ht0b, ht5b, p213_1]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          rcases p213_3 (m.d 0 2) (by simp) with h235 | h235
                                          · rcases p213_3 (m.d 1 2) (by simp) with h236 | h236
                                            · rcases p213_3 (m.d 2 3) (by simp) with h237 | h237
                                              · linarith only [h10, h237, hlam]
                                              · linarith only [h237, h33, hlam]
                                            · linarith only [h236, hlam, p213_0]
                                          · linarith only [h235, h6, hlam]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [h4, hlam, p213_0]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [h10, hlam, p213_0]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [hlam, p213_0]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [h31, hlam, p213_0]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [h10, h13, h4, h7, hc02, hc25, hlam, hphi, ht0b, ht5b, p213_1]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [h5, hlam, p213_0]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [h11, hlam, p213_0]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p213_1]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [hlam, p213_0]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [h0, h11, h33, h35, hc01, hc45, hlam, hphi, ht0b, ht5b, p213_1]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [h6, hlam, p213_0]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [h12, hlam, p213_0]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [h33, hlam, p213_1]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [h34, hlam, p213_0]
                                        · have p213_0 := h213c.1
                                          have p213_1 := h213c.2.1
                                          have p213_2 := h213c.2.2.1
                                          have p213_3 := h213c.2.2.2
                                          linarith only [hlam, p213_0]
                                      · linarith only [h80, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                  · linarith only [h77, h9, hlam]
                                · linarith only [h76, h8, hlam]
                              · linarith only [h6, h75, hlam]
                            · linarith only [h3, h74, hlam]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h3, hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h6, hlam, p36_1]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h8, hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h9, hlam, p36_1]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [hlam, p36_0]
                        · linarith only [h10, h13, h33, h35, hc35, hlam, hphi, u5elo4]
                      · linarith only [h3, h30, h34, hc24, hlam, hphi, ht45, u5elo0]
                    · linarith only [h33, hc23, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h30, hc14, hlam, hphi, ht45, u5elo4]
              · linarith only [h29, hc13, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h12, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h273 | h273
          · rcases m.htr 1 3 4 (by decide) (by decide) with h274 | h274
            · linarith only [h10, h11, h274, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h276 | h276
              · rcases m.htr 1 4 5 (by decide) (by decide) with h277 | h277
                · rcases m.htr 2 3 4 (by decide) (by decide) with h278 | h278
                  · linarith only [h10, h11, h274, h278, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h280 | h280
                    · linarith only [h0, h10, h11, h278, h280, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h280, hc23, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h11, h277, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h276, hc13, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h10, h273, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h286 | h286
        · rcases m.htr 1 2 5 (by decide) (by decide) with h287 | h287
          · rcases m.htr 1 3 4 (by decide) (by decide) with h288 | h288
            · rcases m.htr 1 3 5 (by decide) (by decide) with h289 | h289
              · rcases m.htr 1 4 5 (by decide) (by decide) with h290 | h290
                · rcases m.htr 2 3 4 (by decide) (by decide) with h291 | h291
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h292 | h292
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h293 | h293
                      · linarith only [h0, h10, h286, h293, h4, hc01, hc45, hlam, hphi, ht0b, ht5b]
                      · linarith only [h293, hc24, hlam, hphi, ht45, u5elo4]
                    · linarith only [h10, h292, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h10, h286, h291, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h290, hc14, hlam, hphi, ht45, u5elo4]
              · linarith only [h10, h286, h289, hc24, hlam, hphi, ht45, u5elo3]
            · linarith only [h10, h286, h288, hlam]
          · linarith only [h286, h287, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h302 | h302
          · rcases m.htr 1 3 4 (by decide) (by decide) with h303 | h303
            · rcases m.htr 1 3 5 (by decide) (by decide) with h304 | h304
              · rcases m.htr 1 4 5 (by decide) (by decide) with h305 | h305
                · rcases m.htr 2 3 4 (by decide) (by decide) with h306 | h306
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h307 | h307
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h308 | h308
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h309 | h309
                        · rcases h0bigk with h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h1, h303, h309, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h1, h303, h309, hc01, hc45, hlam, hphi, ht0b, ht5b, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h286, h302, h307, h309, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            rcases p310_3 (m.d 0 1) (by simp) with h315 | h315
                            · rcases p310_3 (m.d 0 2) (by simp) with h316 | h316
                              · linarith only [h0, h316, hlam]
                              · linarith only [h316, h6, hlam]
                            · linarith only [h3, h315, hlam]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h0, hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h286, h302, h306, h307, h309, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h0, h286, h302, h307, h309, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            rcases p310_3 (m.d 0 1) (by simp) with h324 | h324
                            · rcases p310_3 (m.d 0 2) (by simp) with h325 | h325
                              · rcases p310_3 (m.d 0 3) (by simp) with h326 | h326
                                · linarith only [h326, h4, hlam]
                                · linarith only [h326, h8, hlam]
                              · linarith only [h325, h6, hlam]
                            · linarith only [h3, h324, hlam]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h1, hlam, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h4, hlam, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h286, h302, h307, h309, h5, hc03, hc45, hlam, hphi, ht0b, ht5b, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            rcases p310_3 (m.d 0 1) (by simp) with h335 | h335
                            · rcases p310_3 (m.d 0 2) (by simp) with h336 | h336
                              · rcases p310_3 (m.d 0 3) (by simp) with h337 | h337
                                · rcases p310_3 (m.d 0 4) (by simp) with h338 | h338
                                  · linarith only [h338, h7, hlam]
                                  · linarith only [h338, h9, hlam]
                                · linarith only [h337, h8, hlam]
                              · linarith only [h336, h6, hlam]
                            · linarith only [h3, h335, hlam]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h2, hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h5, hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h7, hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            rcases p310_3 (m.d 0 1) (by simp) with h348 | h348
                            · rcases p310_3 (m.d 0 2) (by simp) with h349 | h349
                              · rcases p310_3 (m.d 0 3) (by simp) with h350 | h350
                                · rcases p310_3 (m.d 0 4) (by simp) with h351 | h351
                                  · rcases p310_3 (m.d 0 5) (by simp) with h352 | h352
                                    · linarith only [h352, h9, hlam]
                                    · rcases h0emin with h354 | h354 | h354 | h354 | h354
                                      · rcases h2bigk with h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [hlam, p355_0]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          rcases p355_3 (m.d 0 2) (by simp) with h357 | h357
                                          · rcases p355_3 (m.d 1 2) (by simp) with h358 | h358
                                            · linarith only [h0, h358, hlam]
                                            · rcases p355_3 (m.d 2 3) (by simp) with h360 | h360
                                              · linarith only [h360, h4, hlam]
                                              · linarith only [h10, h360, hlam]
                                          · linarith only [h0, h357, hlam]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [h0, h286, h302, h306, h307, h309, hc01, hc45, hlam, hphi, ht0b, ht5b, p355_1]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [h0, h286, h302, h307, h309, hc01, hc45, hlam, hphi, ht0b, ht5b, p355_1]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [h286, h302, h306, h4, hlam, p355_2]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [h0, hlam, p355_0]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [hlam, p355_0]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [h10, hlam, p355_0]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [h286, hlam, p355_0]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [h286, h306, h307, h309, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p355_1]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [h4, hlam, p355_0]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [h0, h302, h307, h309, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p355_1]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [hlam, p355_0]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [h0, h286, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p355_1]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          rcases p355_3 (m.d 0 2) (by simp) with h376 | h376
                                          · rcases p355_3 (m.d 1 2) (by simp) with h377 | h377
                                            · linarith only [h10, h377, hlam]
                                            · linarith only [h302, h377, hlam]
                                          · linarith only [h376, h6, hlam]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [h5, hlam, p355_0]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [h0, h302, h307, h309, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p355_1]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [h306, hlam, p355_1]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [hlam, p355_0]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          rcases p355_3 (m.d 0 2) (by simp) with h385 | h385
                                          · rcases p355_3 (m.d 1 2) (by simp) with h386 | h386
                                            · linarith only [h286, h386, hlam]
                                            · linarith only [h302, h386, hlam]
                                          · linarith only [h385, h6, hlam]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [h6, hlam, p355_0]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [h302, hlam, p355_0]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [h307, hlam, p355_1]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [h308, hlam, p355_0]
                                        · have p355_0 := h355c.1
                                          have p355_1 := h355c.2.1
                                          have p355_2 := h355c.2.2.1
                                          have p355_3 := h355c.2.2.2
                                          linarith only [hlam, p355_0]
                                      · rcases h2bigk with h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          rcases p395_3 (m.d 0 2) (by simp) with h397 | h397
                                          · rcases p395_3 (m.d 1 2) (by simp) with h398 | h398
                                            · linarith only [h0, h398, hlam]
                                            · rcases p395_3 (m.d 2 3) (by simp) with h400 | h400
                                              · linarith only [h4, h400, hlam]
                                              · linarith only [h10, h400, hlam]
                                          · linarith only [h0, h397, hlam]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h0, h10, h302, h307, h309, hc01, hc45, hlam, hphi, ht0b, ht5b, p395_1]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h0, h286, h302, h307, h309, hc01, hc45, hlam, hphi, ht0b, ht5b, p395_1]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h10, h302, h4, hlam, p395_2]
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
                                          linarith only [h10, hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h286, hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h10, h307, h309, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p395_1]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h4, hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h0, h302, h307, h309, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p395_1]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h0, h286, h302, h307, h309, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p395_1]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          rcases p395_3 (m.d 0 2) (by simp) with h416 | h416
                                          · rcases p395_3 (m.d 1 2) (by simp) with h417 | h417
                                            · linarith only [h10, h417, hlam]
                                            · linarith only [h302, h417, hlam]
                                          · linarith only [h416, h6, hlam]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h5, hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h0, h302, h307, h309, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p395_1]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h306, hlam, p395_1]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          rcases p395_3 (m.d 0 2) (by simp) with h425 | h425
                                          · rcases p395_3 (m.d 1 2) (by simp) with h426 | h426
                                            · linarith only [h286, h426, hlam]
                                            · linarith only [h302, h426, hlam]
                                          · linarith only [h425, h6, hlam]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h6, hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h302, hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h307, hlam, p395_1]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h308, hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [hlam, p395_0]
                                      · rcases h2bigk with h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          rcases p435_3 (m.d 0 2) (by simp) with h437 | h437
                                          · rcases p435_3 (m.d 1 2) (by simp) with h438 | h438
                                            · linarith only [h0, h438, hlam]
                                            · rcases p435_3 (m.d 2 3) (by simp) with h440 | h440
                                              · linarith only [h4, h440, hlam]
                                              · linarith only [h10, h440, hlam]
                                          · linarith only [h0, h437, hlam]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h0, h10, h302, h307, h309, hc01, hc45, hlam, hphi, ht0b, ht5b, p435_1]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h0, h286, h302, h307, h309, hc01, hc45, hlam, hphi, ht0b, ht5b, p435_1]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h10, h302, h4, hlam, p435_2]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h0, hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h10, hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h286, hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h10, h307, h309, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p435_1]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h4, hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h0, h302, h307, h309, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p435_1]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h0, h286, h302, h307, h309, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p435_1]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          rcases p435_3 (m.d 0 2) (by simp) with h456 | h456
                                          · rcases p435_3 (m.d 1 2) (by simp) with h457 | h457
                                            · linarith only [h10, h457, hlam]
                                            · linarith only [h302, h457, hlam]
                                          · linarith only [h456, h6, hlam]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h5, hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h0, h302, h307, h309, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p435_1]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h306, hlam, p435_1]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          rcases p435_3 (m.d 0 2) (by simp) with h465 | h465
                                          · rcases p435_3 (m.d 1 2) (by simp) with h466 | h466
                                            · linarith only [h286, h466, hlam]
                                            · linarith only [h302, h466, hlam]
                                          · linarith only [h465, h6, hlam]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h6, hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h302, hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h307, hlam, p435_1]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [h308, hlam, p435_0]
                                        · have p435_0 := h435c.1
                                          have p435_1 := h435c.2.1
                                          have p435_2 := h435c.2.2.1
                                          have p435_3 := h435c.2.2.2
                                          linarith only [hlam, p435_0]
                                      · rcases h2bigk with h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [hlam, p475_0]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          rcases p475_3 (m.d 0 2) (by simp) with h477 | h477
                                          · rcases p475_3 (m.d 1 2) (by simp) with h478 | h478
                                            · linarith only [h0, h478, hlam]
                                            · rcases p475_3 (m.d 2 3) (by simp) with h480 | h480
                                              · linarith only [h4, h480, hlam]
                                              · linarith only [h10, h480, hlam]
                                          · linarith only [h0, h477, hlam]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [h0, h10, h302, h307, h309, hc01, hc45, hlam, hphi, ht0b, ht5b, p475_1]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [h0, h286, h302, h307, h309, hc01, hc45, hlam, hphi, ht0b, ht5b, p475_1]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [h10, h302, h4, hlam, p475_2]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [h0, hlam, p475_0]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [hlam, p475_0]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [h10, hlam, p475_0]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [h286, hlam, p475_0]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [h10, h307, h309, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p475_1]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [h4, hlam, p475_0]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [h0, h302, h307, h309, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p475_1]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [hlam, p475_0]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [h0, h286, h302, h307, h309, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p475_1]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          rcases p475_3 (m.d 0 2) (by simp) with h496 | h496
                                          · rcases p475_3 (m.d 1 2) (by simp) with h497 | h497
                                            · linarith only [h10, h497, hlam]
                                            · linarith only [h302, h497, hlam]
                                          · linarith only [h496, h6, hlam]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [h5, hlam, p475_0]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [h0, h302, h307, h309, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p475_1]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [h306, hlam, p475_1]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [hlam, p475_0]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          rcases p475_3 (m.d 0 2) (by simp) with h505 | h505
                                          · rcases p475_3 (m.d 1 2) (by simp) with h506 | h506
                                            · linarith only [h286, h506, hlam]
                                            · linarith only [h302, h506, hlam]
                                          · linarith only [h505, h6, hlam]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [h6, hlam, p475_0]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [h302, hlam, p475_0]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [h307, hlam, p475_1]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [h308, hlam, p475_0]
                                        · have p475_0 := h475c.1
                                          have p475_1 := h475c.2.1
                                          have p475_2 := h475c.2.2.1
                                          have p475_3 := h475c.2.2.2
                                          linarith only [hlam, p475_0]
                                      · linarith only [h354, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                  · linarith only [h351, h9, hlam]
                                · linarith only [h350, h8, hlam]
                              · linarith only [h349, h6, hlam]
                            · linarith only [h3, h348, hlam]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h3, hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h6, hlam, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h8, hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h9, hlam, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [hlam, p310_0]
                        · linarith only [h309, hc34, hlam, hphi, ht45, u5elo4]
                      · linarith only [h308, hc24, hlam, hphi, ht45, u5elo4]
                    · linarith only [h307, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h0, h10, h302, h306, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h305, hc14, hlam, hphi, ht45, u5elo4]
              · linarith only [h304, hc13, hlam, hphi, ht34, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h531 | h531
              · rcases m.htr 1 4 5 (by decide) (by decide) with h532 | h532
                · rcases m.htr 2 3 4 (by decide) (by decide) with h533 | h533
                  · linarith only [h0, h10, h302, h303, h4, h533, hc01, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h10, h302, h4, h533, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h10, h302, h303, h532, hc25, hlam, hphi, u5elo4]
              · linarith only [h10, h302, h531, hc25, hlam, hphi, u5elo3]
          · linarith only [h302, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · linarith only [h9, hc04, hlam, hphi, ht45, u5elo4]
  · linarith only [h8, hc03, hlam, hphi, ht34, ht45, u5elo3]

end R2N4
