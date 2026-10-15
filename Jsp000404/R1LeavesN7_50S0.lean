import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5456000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_M_IR_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
    · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
              · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                            · linarith only [h0, h15, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h15, h6, hc23, hlam, hphi, u3elo0]
                          · linarith only [h14, h5, hc23, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                            · linarith only [h0, h20, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h20, h6, hc23, hlam, hphi, u3elo0]
                          · linarith only [h19, h5, hc23, hlam, hphi, u3elo0]
                      · linarith only [h12, h6, hc13, hlam, hphi, u3elo0]
                    · linarith only [h11, h5, h8, hc23, hlam, hphi, u3elo0]
                  · linarith only [h10, h4, h5, h7, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h3, h5, h8, h9, hc23, hlam, hphi, u3elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                  · linarith only [h29, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
                        · linarith only [h28, h29, h33, h4, h5, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                              · linarith only [h28, h29, h33, h37, h4, h5, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                              · linarith only [h29, h37, h5, h7, hc12, hlam, hphi, ht23, u3elo0]
                            · linarith only [h32, h36, hc23, hlam, hphi, u3elo1]
                          · linarith only [h35, h5, h8, hc13, hlam, hphi, u3elo0]
                      · linarith only [h32, h6, h8, hc12, hlam, hphi, ht23, u3elo0]
                    · linarith only [h28, h31, h5, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
                  · linarith only [h44, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h46 | h46
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h47 | h47
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h48 | h48
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h50 | h50
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h51 | h51
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h52 | h52
                                · linarith only [h46, h52, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                                · rcases h0emin with h54 | h54 | h54 | h54 | h54
                                  · rcases h2bigk with h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [hlam, p55_0]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      rcases p55_3 (m.d 0 2) (by simp) with h57 | h57
                                      · rcases p55_3 (m.d 1 2) (by simp) with h58 | h58
                                        · linarith only [h0, h58, hlam]
                                        · rcases p55_3 (m.d 2 3) (by simp) with h60 | h60
                                          · linarith only [h2, h60, hlam]
                                          · linarith only [h60, h8, hlam]
                                      · linarith only [h0, h57, hlam]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [h0, h46, h48, h52, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p55_1]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [h0, h28, h48, h52, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p55_1]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      rcases p55_3 (m.d 0 2) (by simp) with h66 | h66
                                      · rcases p55_3 (m.d 1 2) (by simp) with h67 | h67
                                        · linarith only [h0, h67, hlam]
                                        · rcases p55_3 (m.d 2 3) (by simp) with h69 | h69
                                          · linarith only [h2, h69, hlam]
                                          · linarith only [h50, h69, hlam]
                                      · linarith only [h66, hlam, p55_0]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [h0, hlam, p55_0]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [hlam, p55_0]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [h8, hlam, p55_0]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [h28, hlam, p55_0]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [h44, hlam, p55_0]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [h2, hlam, p55_0]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht23, p55_1, u3elo2]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [hlam, p55_0]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [h2, h28, h48, h52, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p55_1, u3elo0]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p55_1, u3elo0, u5ehi2]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [h3, hlam, p55_0]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [h3, h5, hc12, hlam, hphi, ht23, p55_1, u3elo0]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [h49, hlam, p55_1]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [hlam, p55_0]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [h3, h44, h5, hc12, hlam, hphi, ht23, p55_1, u3elo0]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [h4, hlam, p55_0]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [h4, h5, h7, hc12, hlam, hphi, ht23, p55_1, u3elo0]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [h50, hlam, p55_1]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [h51, hlam, p55_0]
                                    · have p55_0 := h55c.1
                                      have p55_1 := h55c.2.1
                                      have p55_2 := h55c.2.2.1
                                      have p55_3 := h55c.2.2.2
                                      linarith only [hlam, p55_0]
                                  · rcases h2bigk with h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [hlam, p93_0]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      rcases p93_3 (m.d 0 2) (by simp) with h95 | h95
                                      · rcases p93_3 (m.d 1 2) (by simp) with h96 | h96
                                        · linarith only [h0, h96, hlam]
                                        · rcases p93_3 (m.d 2 3) (by simp) with h98 | h98
                                          · linarith only [h2, h98, hlam]
                                          · linarith only [h8, h98, hlam]
                                      · linarith only [h0, h95, hlam]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [h0, h46, h48, h52, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p93_1]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [h0, h28, h48, h52, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p93_1]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      rcases p93_3 (m.d 0 2) (by simp) with h104 | h104
                                      · rcases p93_3 (m.d 1 2) (by simp) with h105 | h105
                                        · linarith only [h0, h105, hlam]
                                        · rcases p93_3 (m.d 2 3) (by simp) with h107 | h107
                                          · linarith only [h107, h2, hlam]
                                          · linarith only [h107, h50, hlam]
                                      · linarith only [h104, hlam, p93_0]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [h0, hlam, p93_0]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [hlam, p93_0]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [h8, hlam, p93_0]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [h28, hlam, p93_0]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [h44, hlam, p93_0]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [h2, hlam, p93_0]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht23, p93_1, u3elo2]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [hlam, p93_0]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [h2, h28, h48, h52, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p93_1, u3elo0]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p93_1, u3elo0, u5ehi2]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [h3, hlam, p93_0]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [h3, h5, hc12, hlam, hphi, ht23, p93_1, u3elo0]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [h49, hlam, p93_1]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [hlam, p93_0]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [h3, h44, h5, hc12, hlam, hphi, ht23, p93_1, u3elo0]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [h4, hlam, p93_0]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [h4, h5, h7, hc12, hlam, hphi, ht23, p93_1, u3elo0]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [h50, hlam, p93_1]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [h51, hlam, p93_0]
                                    · have p93_0 := h93c.1
                                      have p93_1 := h93c.2.1
                                      have p93_2 := h93c.2.2.1
                                      have p93_3 := h93c.2.2.2
                                      linarith only [hlam, p93_0]
                                  · linarith only [h54, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h5, h54, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h5, h54, h7, hlam, ht01, ht12, ht23, u3elo0]
                              · linarith only [h28, h46, h48, h51, hc12, hlam, hphi, ht23, u3elo1]
                            · linarith only [h46, h48, h50, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                          · linarith only [h46, h48, h49, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi4]
                        · linarith only [h28, h48, h5, h7, hc12, hlam, hphi, ht23, u3elo0]
                      · linarith only [h47, h6, hc13, hlam, hphi, u3elo0]
                    · linarith only [h46, h5, h8, hc12, hlam, hphi, ht23, u3elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h140 | h140
              · rcases m.htr 1 2 4 (by decide) (by decide) with h141 | h141
                · rcases m.htr 1 2 5 (by decide) (by decide) with h142 | h142
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h144 | h144
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h145 | h145
                        · linarith only [h1, h145, h7, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h147 | h147
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h148 | h148
                            · linarith only [h0, h140, h148, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h148, h6, hc23, hlam, hphi, u3elo0]
                          · linarith only [h147, h5, hc23, hlam, hphi, u3elo0]
                      · linarith only [h144, h6, hc13, hlam, hphi, u3elo0]
                    · linarith only [h140, h143, h5, hc23, hlam, hphi, u3elo0]
                  · linarith only [h140, h142, h4, h6, hc23, hlam, hphi, u3elo0]
                · linarith only [h140, h141, h3, h5, hc23, hlam, hphi, u3elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h156 | h156
                · rcases m.htr 1 2 5 (by decide) (by decide) with h157 | h157
                  · linarith only [h140, h157, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h159 | h159
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h160 | h160
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h161 | h161
                        · linarith only [h156, h157, h161, h4, h6, h7, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h163 | h163
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h164 | h164
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h165 | h165
                              · linarith only [h157, h165, h3, h4, h5, h7, hc12, hlam, hphi, ht23, u3elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h167 | h167
                                · linarith only [h157, h167, h4, h7, hc12, hlam, hphi, ht23, u3elo3]
                                · rcases h0emin with h169 | h169 | h169 | h169 | h169
                                  · rcases h2bigk with h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [hlam, p170_0]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      rcases p170_3 (m.d 0 2) (by simp) with h172 | h172
                                      · rcases p170_3 (m.d 1 2) (by simp) with h173 | h173
                                        · linarith only [h0, h173, hlam]
                                        · rcases p170_3 (m.d 2 3) (by simp) with h175 | h175
                                          · linarith only [h175, h2, hlam]
                                          · linarith only [h140, h175, hlam]
                                      · linarith only [h0, h172, hlam]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [h0, h156, h157, h163, h164, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p170_1]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [h156, h157, h164, h2, hlam, p170_2]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [h156, h157, h163, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p170_1]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [h0, hlam, p170_0]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [hlam, p170_0]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [h140, hlam, p170_0]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [h157, h163, h4, h7, hc34, hc45, hlam, hphi, p170_1]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [h157, hlam, p170_0]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [h2, hlam, p170_0]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht23, p170_1, u3elo0]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [hlam, p170_0]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      rcases p170_3 (m.d 0 2) (by simp) with h190 | h190
                                      · rcases p170_3 (m.d 1 2) (by simp) with h191 | h191
                                        · linarith only [h140, h191, hlam]
                                        · linarith only [h156, h191, hlam]
                                      · linarith only [h190, h3, hlam]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [h157, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p170_1, u3elo0, u5ehi1]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [h3, hlam, p170_0]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [h156, hlam, p170_0]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [h163, hlam, p170_1]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [hlam, p170_0]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [h165, hlam, p170_1]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [h4, hlam, p170_0]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [h0, h156, h163, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p170_1]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [h164, hlam, p170_1]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      rcases p170_3 (m.d 0 2) (by simp) with h204 | h204
                                      · rcases p170_3 (m.d 1 2) (by simp) with h205 | h205
                                        · linarith only [h157, h205, hlam]
                                        · linarith only [h156, h205, hlam]
                                      · linarith only [h204, h3, hlam]
                                    · have p170_0 := h170c.1
                                      have p170_1 := h170c.2.1
                                      have p170_2 := h170c.2.2.1
                                      have p170_3 := h170c.2.2.2
                                      linarith only [hlam, p170_0]
                                  · rcases h2bigk with h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [hlam, p210_0]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      rcases p210_3 (m.d 0 2) (by simp) with h212 | h212
                                      · rcases p210_3 (m.d 1 2) (by simp) with h213 | h213
                                        · linarith only [h0, h213, hlam]
                                        · rcases p210_3 (m.d 2 3) (by simp) with h215 | h215
                                          · linarith only [h2, h215, hlam]
                                          · linarith only [h140, h215, hlam]
                                      · linarith only [h0, h212, hlam]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [h0, h140, h156, h163, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p210_1]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [h140, h156, h2, hlam, p210_2]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [h156, h157, h163, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p210_1]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [h0, hlam, p210_0]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [hlam, p210_0]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [h140, hlam, p210_0]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [h140, h163, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p210_1, u3elo2]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [h157, hlam, p210_0]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [h2, hlam, p210_0]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht23, p210_1, u3elo2]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [hlam, p210_0]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      rcases p210_3 (m.d 0 2) (by simp) with h230 | h230
                                      · rcases p210_3 (m.d 1 2) (by simp) with h231 | h231
                                        · linarith only [h140, h231, hlam]
                                        · linarith only [h156, h231, hlam]
                                      · linarith only [h230, h3, hlam]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [h156, h157, h163, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p210_1, u3elo0]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [h3, hlam, p210_0]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [h156, hlam, p210_0]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [h163, hlam, p210_1]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [hlam, p210_0]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [h165, hlam, p210_1]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [h4, hlam, p210_0]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [h0, h156, h163, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p210_1]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [h164, hlam, p210_1]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      rcases p210_3 (m.d 0 2) (by simp) with h244 | h244
                                      · rcases p210_3 (m.d 1 2) (by simp) with h245 | h245
                                        · linarith only [h157, h245, hlam]
                                        · linarith only [h156, h245, hlam]
                                      · linarith only [h244, h3, hlam]
                                    · have p210_0 := h210c.1
                                      have p210_1 := h210c.2.1
                                      have p210_2 := h210c.2.2.1
                                      have p210_3 := h210c.2.2.2
                                      linarith only [hlam, p210_0]
                                  · linarith only [h169, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h169, h5, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h169, h6, hlam, ht01, ht12, ht23, u3elo0]
                            · linarith only [h140, h164, h6, hc13, hlam, hphi, u3elo0]
                          · linarith only [h140, h163, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h160, h6, hc13, hlam, hphi, u3elo0]
                    · linarith only [h140, h156, h159, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h257 | h257
                  · linarith only [h156, h257, h3, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h259 | h259
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h260 | h260
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h261 | h261
                        · linarith only [h156, h261, h3, h7, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h263 | h263
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h264 | h264
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h265 | h265
                              · linarith only [h265, h3, h7, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h267 | h267
                                · linarith only [h267, h3, h5, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                                · rcases h0emin with h269 | h269 | h269 | h269 | h269
                                  · rcases h2bigk with h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      rcases p270_3 (m.d 0 2) (by simp) with h272 | h272
                                      · rcases p270_3 (m.d 1 2) (by simp) with h273 | h273
                                        · linarith only [h0, h273, hlam]
                                        · rcases p270_3 (m.d 2 3) (by simp) with h275 | h275
                                          · linarith only [h2, h275, hlam]
                                          · linarith only [h140, h275, hlam]
                                      · linarith only [h0, h272, hlam]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h0, h140, h260, hc01, hlam, hphi, ht0b, ht5b, p270_1, u5ehi3]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      rcases p270_3 (m.d 0 2) (by simp) with h280 | h280
                                      · rcases p270_3 (m.d 1 2) (by simp) with h281 | h281
                                        · linarith only [h0, h281, hlam]
                                        · rcases p270_3 (m.d 2 3) (by simp) with h283 | h283
                                          · linarith only [h2, h283, hlam]
                                          · linarith only [h263, h283, hlam]
                                      · linarith only [h280, hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      rcases p270_3 (m.d 0 2) (by simp) with h287 | h287
                                      · rcases p270_3 (m.d 1 2) (by simp) with h288 | h288
                                        · linarith only [h0, h288, hlam]
                                        · rcases p270_3 (m.d 2 3) (by simp) with h290 | h290
                                          · linarith only [h2, h290, hlam]
                                          · linarith only [h264, h290, hlam]
                                      · linarith only [h287, hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h0, hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h140, hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h156, hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h257, hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h2, hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht23, p270_1, u3elo2]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h156, h2, hc12, hlam, hphi, ht23, p270_1, u3elo0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h156, h2, h265, hc12, hlam, hphi, ht23, p270_1, u3elo0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h3, hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h3, h7, hc12, hc45, hlam, hphi, ht23, ht34, p270_1]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h263, hlam, p270_1]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h265, hlam, p270_1]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h4, hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h4, h6, hc12, hlam, hphi, ht23, p270_1, u3elo0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h264, hlam, p270_1]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h156, h4, h6, hc12, hlam, hphi, ht23, p270_1, u3elo0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [hlam, p270_0]
                                  · rcases h2bigk with h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [hlam, p314_0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      rcases p314_3 (m.d 0 2) (by simp) with h316 | h316
                                      · rcases p314_3 (m.d 1 2) (by simp) with h317 | h317
                                        · linarith only [h0, h317, hlam]
                                        · rcases p314_3 (m.d 2 3) (by simp) with h319 | h319
                                          · linarith only [h2, h319, hlam]
                                          · linarith only [h140, h319, hlam]
                                      · linarith only [h0, h316, hlam]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [h140, h260, hc02, hlam, hphi, ht0b, ht5b, p314_1, u5ehi3]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      rcases p314_3 (m.d 0 2) (by simp) with h324 | h324
                                      · rcases p314_3 (m.d 1 2) (by simp) with h325 | h325
                                        · linarith only [h0, h325, hlam]
                                        · rcases p314_3 (m.d 2 3) (by simp) with h327 | h327
                                          · linarith only [h2, h327, hlam]
                                          · linarith only [h263, h327, hlam]
                                      · linarith only [h324, hlam, p314_0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      rcases p314_3 (m.d 0 2) (by simp) with h331 | h331
                                      · rcases p314_3 (m.d 1 2) (by simp) with h332 | h332
                                        · linarith only [h0, h332, hlam]
                                        · rcases p314_3 (m.d 2 3) (by simp) with h334 | h334
                                          · linarith only [h2, h334, hlam]
                                          · linarith only [h264, h334, hlam]
                                      · linarith only [h331, hlam, p314_0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [h0, hlam, p314_0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [hlam, p314_0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [h140, hlam, p314_0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [h156, hlam, p314_0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [h257, hlam, p314_0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [h2, hlam, p314_0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht23, p314_1, u3elo0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [hlam, p314_0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [h156, h2, hc12, hlam, hphi, ht23, p314_1, u3elo0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p314_1, u3elo0, u5ehi2]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [h3, hlam, p314_0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [h3, h6, h7, hc12, hlam, hphi, ht23, p314_1, u3elo0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [h263, hlam, p314_1]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [hlam, p314_0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [h265, hlam, p314_1]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [h4, hlam, p314_0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [h4, h6, hc12, hlam, hphi, ht23, p314_1, u3elo0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [h264, hlam, p314_1]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [h156, h4, h6, hc12, hlam, hphi, ht23, p314_1, u3elo0]
                                    · have p314_0 := h314c.1
                                      have p314_1 := h314c.2.1
                                      have p314_2 := h314c.2.2.1
                                      have p314_3 := h314c.2.2.2
                                      linarith only [hlam, p314_0]
                                  · linarith only [h269, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h269, h7, hc45, hlam, ht01, ht12, ht23, ht34]
                                  · linarith only [h269, h6, hlam, ht01, ht12, ht23, u3elo0]
                            · linarith only [h140, h260, h264, hlam]
                          · linarith only [h140, h260, h263, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                      · linarith only [h260, h6, hc13, hlam, hphi, u3elo0]
                    · linarith only [h140, h259, h5, hc12, hlam, hphi, ht23, u3elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h365 | h365
            · linarith only [h365, h5, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h367 | h367
              · rcases m.htr 1 2 4 (by decide) (by decide) with h368 | h368
                · rcases m.htr 1 2 5 (by decide) (by decide) with h369 | h369
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h370 | h370
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h371 | h371
                      · linarith only [h371, h6, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h373 | h373
                        · linarith only [h365, h370, h371, h373, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h375 | h375
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h376 | h376
                            · linarith only [h2, h371, h376, hc13, hlam, hphi, u3elo0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h378 | h378
                              · linarith only [h3, h365, h378, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h380 | h380
                                · linarith only [h2, h365, h375, h380, h6, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · rcases h0emin with h382 | h382 | h382 | h382 | h382
                                  · rcases h2bigk with h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [hlam, p383_0]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [h0, h369, hc01, hlam, hphi, ht0b, ht5b, p383_1, u5ehi2]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      rcases p383_3 (m.d 0 2) (by simp) with h386 | h386
                                      · rcases p383_3 (m.d 1 2) (by simp) with h387 | h387
                                        · linarith only [h0, h387, hlam]
                                        · linarith only [h367, h387, hlam]
                                      · linarith only [h386, hlam, p383_0]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      rcases p383_3 (m.d 0 2) (by simp) with h391 | h391
                                      · rcases p383_3 (m.d 1 2) (by simp) with h392 | h392
                                        · linarith only [h0, h392, hlam]
                                        · linarith only [h368, h392, hlam]
                                      · linarith only [h391, hlam, p383_0]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      rcases p383_3 (m.d 0 2) (by simp) with h396 | h396
                                      · rcases p383_3 (m.d 1 2) (by simp) with h397 | h397
                                        · linarith only [h0, h397, hlam]
                                        · linarith only [h369, h397, hlam]
                                      · linarith only [h396, hlam, p383_0]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [h0, hlam, p383_0]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [hlam, p383_0]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [h0, h375, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p383_1]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      rcases p383_3 (m.d 0 2) (by simp) with h404 | h404
                                      · rcases p383_3 (m.d 1 2) (by simp) with h405 | h405
                                        · rcases p383_3 (m.d 2 3) (by simp) with h406 | h406
                                          · linarith only [h367, h406, hlam]
                                          · linarith only [h375, h406, hlam]
                                        · linarith only [h405, hlam, p383_0]
                                      · linarith only [h3, h404, hlam]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [h0, h375, h376, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p383_1]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [h2, hlam, p383_0]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [h367, hlam, p383_0]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [hlam, p383_0]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [h2, h375, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p383_1, u3elo4]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [h376, hlam, p383_0]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [h3, hlam, p383_0]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [h368, hlam, p383_0]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [h375, hlam, p383_1]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [hlam, p383_0]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [h378, hlam, p383_1]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [h4, hlam, p383_0]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [h369, hlam, p383_0]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [h4, h6, hc23, hlam, hphi, p383_1, u3elo4]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [h0, h369, h375, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p383_1]
                                    · have p383_0 := h383c.1
                                      have p383_1 := h383c.2.1
                                      have p383_2 := h383c.2.2.1
                                      have p383_3 := h383c.2.2.2
                                      linarith only [hlam, p383_0]
                                  · rcases h2bigk with h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h0, h369, hc01, hlam, hphi, ht0b, ht5b, p427_1, u5ehi2]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      rcases p427_3 (m.d 0 2) (by simp) with h430 | h430
                                      · rcases p427_3 (m.d 1 2) (by simp) with h431 | h431
                                        · linarith only [h0, h431, hlam]
                                        · linarith only [h367, h431, hlam]
                                      · linarith only [h430, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      rcases p427_3 (m.d 0 2) (by simp) with h435 | h435
                                      · rcases p427_3 (m.d 1 2) (by simp) with h436 | h436
                                        · linarith only [h0, h436, hlam]
                                        · linarith only [h368, h436, hlam]
                                      · linarith only [h435, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      rcases p427_3 (m.d 0 2) (by simp) with h440 | h440
                                      · rcases p427_3 (m.d 1 2) (by simp) with h441 | h441
                                        · linarith only [h0, h441, hlam]
                                        · linarith only [h369, h441, hlam]
                                      · linarith only [h440, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h0, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h0, h375, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p427_1]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      rcases p427_3 (m.d 0 2) (by simp) with h448 | h448
                                      · rcases p427_3 (m.d 1 2) (by simp) with h449 | h449
                                        · rcases p427_3 (m.d 2 3) (by simp) with h450 | h450
                                          · linarith only [h367, h450, hlam]
                                          · linarith only [h375, h450, hlam]
                                        · linarith only [h449, hlam, p427_0]
                                      · linarith only [h3, h448, hlam]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h0, h375, h376, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p427_1]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h2, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h367, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h2, h375, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p427_1, u3elo4]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h376, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h3, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h368, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h375, hlam, p427_1]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h378, hlam, p427_1]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h4, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h369, hlam, p427_0]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h4, h6, hc23, hlam, hphi, p427_1, u3elo4]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [h0, h369, h375, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p427_1]
                                    · have p427_0 := h427c.1
                                      have p427_1 := h427c.2.1
                                      have p427_2 := h427c.2.2.1
                                      have p427_3 := h427c.2.2.2
                                      linarith only [hlam, p427_0]
                                  · linarith only [h382, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h382, h5, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h382, h6, hlam, ht01, ht12, ht23, u3elo4]
                          · linarith only [h375, h5, h6, hc23, hlam, hphi, u3elo4]
                    · linarith only [h367, h370, h5, h6, hc23, hlam, hphi, u3elo4]
                  · linarith only [h367, h369, h4, h6, hc23, hlam, hphi, u3elo4]
                · linarith only [h3, h367, h368, h5, h6, hc23, hlam, hphi, u3elo4]
              · linarith only [h2, h367, h6, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h479 | h479
          · linarith only [h479, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h481 | h481
            · rcases m.htr 1 2 3 (by decide) (by decide) with h482 | h482
              · rcases m.htr 1 2 4 (by decide) (by decide) with h483 | h483
                · rcases m.htr 1 2 5 (by decide) (by decide) with h484 | h484
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h485 | h485
                    · linarith only [h485, h5, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h487 | h487
                      · linarith only [h479, h485, h487, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h489 | h489
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h490 | h490
                          · linarith only [h2, h485, h490, hc13, hlam, hphi, u3elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h492 | h492
                            · linarith only [h2, h487, h492, h5, hc13, hlam, hphi, u3elo3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h494 | h494
                              · linarith only [h0, h483, h494, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h481, h490, h494, h5, hc23, hlam, hphi, u3elo3]
                        · linarith only [h481, h482, h485, h489, h5, hc23, hlam, hphi, u3elo3]
                  · linarith only [h4, h481, h482, h484, h5, hc23, hlam, hphi, u3elo3]
                · linarith only [h3, h482, h483, h5, hc23, hlam, hphi, u3elo3]
              · linarith only [h2, h482, h5, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h501 | h501
              · rcases m.htr 1 2 4 (by decide) (by decide) with h502 | h502
                · rcases m.htr 1 2 5 (by decide) (by decide) with h503 | h503
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h504 | h504
                    · linarith only [h5, h504, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h506 | h506
                      · linarith only [h479, h504, h506, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h508 | h508
                        · linarith only [h2, h481, h5, h504, h508, hc23, hlam, hphi, u3elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h510 | h510
                          · linarith only [h2, h5, h510, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h512 | h512
                            · linarith only [h2, h479, h512, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h514 | h514
                              · linarith only [h3, h481, h514, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h516 | h516
                                · linarith only [h481, h5, h516, hc03, hlam, hphi, u3elo3]
                                · rcases h0emin with h518 | h518 | h518 | h518 | h518
                                  · rcases h2bigk with h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [hlam, p519_0]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [h0, h503, hc01, hlam, hphi, ht0b, ht5b, p519_1, u5ehi2]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      rcases p519_3 (m.d 0 2) (by simp) with h522 | h522
                                      · rcases p519_3 (m.d 1 2) (by simp) with h523 | h523
                                        · linarith only [h0, h523, hlam]
                                        · linarith only [h501, h523, hlam]
                                      · linarith only [h522, hlam, p519_0]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      rcases p519_3 (m.d 0 2) (by simp) with h527 | h527
                                      · rcases p519_3 (m.d 1 2) (by simp) with h528 | h528
                                        · linarith only [h0, h528, hlam]
                                        · linarith only [h502, h528, hlam]
                                      · linarith only [h527, hlam, p519_0]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      rcases p519_3 (m.d 0 2) (by simp) with h532 | h532
                                      · rcases p519_3 (m.d 1 2) (by simp) with h533 | h533
                                        · linarith only [h0, h533, hlam]
                                        · linarith only [h503, h533, hlam]
                                      · linarith only [h532, hlam, p519_0]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [h0, hlam, p519_0]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [hlam, p519_0]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      rcases p519_3 (m.d 0 2) (by simp) with h539 | h539
                                      · rcases p519_3 (m.d 1 2) (by simp) with h540 | h540
                                        · rcases p519_3 (m.d 2 3) (by simp) with h541 | h541
                                          · linarith only [h541, hlam, p519_0]
                                          · rcases p519_3 (m.d 2 4) (by simp) with h543 | h543
                                            · linarith only [h502, h543, hlam]
                                            · linarith only [h510, h543, hlam]
                                        · linarith only [h540, hlam, p519_0]
                                      · linarith only [h2, h539, hlam]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      rcases p519_3 (m.d 0 2) (by simp) with h548 | h548
                                      · rcases p519_3 (m.d 1 2) (by simp) with h549 | h549
                                        · rcases p519_3 (m.d 2 3) (by simp) with h550 | h550
                                          · linarith only [h501, h550, hlam]
                                          · rcases p519_3 (m.d 2 4) (by simp) with h552 | h552
                                            · linarith only [h552, hlam, p519_0]
                                            · rcases p519_3 (m.d 2 5) (by simp) with h554 | h554
                                              · linarith only [h503, h554, hlam]
                                              · linarith only [h514, h554, hlam]
                                        · linarith only [h549, hlam, p519_0]
                                      · linarith only [h3, h548, hlam]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p519_1, u5ehi2]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [h2, hlam, p519_0]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [h501, hlam, p519_0]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [hlam, p519_0]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [h510, hlam, p519_0]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [h512, hlam, p519_0]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [h3, hlam, p519_0]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [h502, hlam, p519_0]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [h3, h5, hc23, hlam, hphi, p519_1, u3elo3]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [hlam, p519_0]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [h514, hlam, p519_1]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [h4, hlam, p519_0]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [h503, hlam, p519_0]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [h4, h479, hc23, hlam, hphi, p519_1, u3elo4]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [h0, h503, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p519_1]
                                    · have p519_0 := h519c.1
                                      have p519_1 := h519c.2.1
                                      have p519_2 := h519c.2.2.1
                                      have p519_3 := h519c.2.2.2
                                      linarith only [hlam, p519_0]
                                  · rcases h2bigk with h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [hlam, p575_0]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [h0, h503, hc01, hlam, hphi, ht0b, ht5b, p575_1, u5ehi2]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      rcases p575_3 (m.d 0 2) (by simp) with h578 | h578
                                      · rcases p575_3 (m.d 1 2) (by simp) with h579 | h579
                                        · linarith only [h0, h579, hlam]
                                        · linarith only [h501, h579, hlam]
                                      · linarith only [h578, hlam, p575_0]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      rcases p575_3 (m.d 0 2) (by simp) with h583 | h583
                                      · rcases p575_3 (m.d 1 2) (by simp) with h584 | h584
                                        · linarith only [h0, h584, hlam]
                                        · linarith only [h502, h584, hlam]
                                      · linarith only [h583, hlam, p575_0]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      rcases p575_3 (m.d 0 2) (by simp) with h588 | h588
                                      · rcases p575_3 (m.d 1 2) (by simp) with h589 | h589
                                        · linarith only [h0, h589, hlam]
                                        · linarith only [h503, h589, hlam]
                                      · linarith only [h588, hlam, p575_0]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [h0, hlam, p575_0]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [hlam, p575_0]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      rcases p575_3 (m.d 0 2) (by simp) with h595 | h595
                                      · rcases p575_3 (m.d 1 2) (by simp) with h596 | h596
                                        · rcases p575_3 (m.d 2 3) (by simp) with h597 | h597
                                          · linarith only [h597, hlam, p575_0]
                                          · rcases p575_3 (m.d 2 4) (by simp) with h599 | h599
                                            · linarith only [h502, h599, hlam]
                                            · linarith only [h510, h599, hlam]
                                        · linarith only [h596, hlam, p575_0]
                                      · linarith only [h2, h595, hlam]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      rcases p575_3 (m.d 0 2) (by simp) with h604 | h604
                                      · rcases p575_3 (m.d 1 2) (by simp) with h605 | h605
                                        · rcases p575_3 (m.d 2 3) (by simp) with h606 | h606
                                          · linarith only [h501, h606, hlam]
                                          · rcases p575_3 (m.d 2 4) (by simp) with h608 | h608
                                            · linarith only [h608, hlam, p575_0]
                                            · rcases p575_3 (m.d 2 5) (by simp) with h610 | h610
                                              · linarith only [h503, h610, hlam]
                                              · linarith only [h514, h610, hlam]
                                        · linarith only [h605, hlam, p575_0]
                                      · linarith only [h3, h604, hlam]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p575_1, u5ehi2]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [h2, hlam, p575_0]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [h501, hlam, p575_0]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [hlam, p575_0]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [h510, hlam, p575_0]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [h512, hlam, p575_0]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [h3, hlam, p575_0]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [h502, hlam, p575_0]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [h3, h5, h516, hc23, hc45, hlam, hphi, ht34, p575_1]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [hlam, p575_0]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [h514, hlam, p575_1]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [h4, hlam, p575_0]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [h503, hlam, p575_0]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [h4, h479, hc23, hlam, hphi, p575_1, u3elo4]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [h0, h503, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p575_1]
                                    · have p575_0 := h575c.1
                                      have p575_1 := h575c.2.1
                                      have p575_2 := h575c.2.2.1
                                      have p575_3 := h575c.2.2.2
                                      linarith only [hlam, p575_0]
                                  · linarith only [h518, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h5, h516, h518, hc45, hlam, ht01, ht12, ht23, ht34]
                                  · linarith only [h479, h518, hlam, ht01, ht12, ht23, u3elo4]
                  · linarith only [h4, h479, h501, h503, hc23, hlam, hphi, u3elo4]
                · linarith only [h3, h479, h481, h501, h502, hc23, hlam, hphi, u3elo4]
              · linarith only [h2, h5, h501, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h637 | h637
        · rcases m.htr 0 3 5 (by decide) (by decide) with h638 | h638
          · linarith only [h2, h4, h638, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h640 | h640
            · linarith only [h637, h638, h640, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h642 | h642
              · rcases m.htr 1 2 4 (by decide) (by decide) with h643 | h643
                · rcases m.htr 1 2 5 (by decide) (by decide) with h644 | h644
                  · linarith only [h0, h4, h644, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h646 | h646
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h647 | h647
                      · linarith only [h638, h647, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h649 | h649
                        · linarith only [h640, h646, h647, h649, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h651 | h651
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h652 | h652
                            · linarith only [h2, h647, h652, hc13, hlam, hphi, u3elo0]
                            · linarith only [h0, h4, h642, h652, hc23, hlam, hphi, u3elo4]
                          · linarith only [h646, h651, hc23, hlam, hphi, u3elo1]
                    · linarith only [h637, h638, h646, hc13, hlam, hphi, u3elo4]
                · linarith only [h3, h4, h642, h643, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · linarith only [h2, h4, h638, h642, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h659 | h659
          · linarith only [h637, h659, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h661 | h661
            · linarith only [h3, h4, h661, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h663 | h663
              · rcases m.htr 1 2 4 (by decide) (by decide) with h664 | h664
                · rcases m.htr 1 2 5 (by decide) (by decide) with h665 | h665
                  · linarith only [h0, h4, h665, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h667 | h667
                    · linarith only [h637, h667, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h669 | h669
                      · linarith only [h0, h4, h659, h664, h667, h669, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h671 | h671
                        · linarith only [h0, h2, h4, h637, h659, h661, h664, h671, hc23, hlam, hphi, u3elo4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h673 | h673
                          · linarith only [h2, h667, h673, hc13, hlam, hphi, u3elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h675 | h675
                            · linarith only [h0, h2, h4, h637, h659, h664, h675, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                            · linarith only [h0, h4, h664, h673, h675, hc23, hlam, hphi, u3elo4]
                · linarith only [h3, h4, h664, hc12, hc25, hlam, hphi]
              · linarith only [h2, h4, h659, h663, hc12, hlam, hphi, ht23, u3elo4]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h680 | h680
      · rcases m.htr 0 3 4 (by decide) (by decide) with h681 | h681
        · linarith only [h2, h3, h681, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h683 | h683
          · linarith only [h681, h683, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h685 | h685
            · rcases m.htr 1 2 3 (by decide) (by decide) with h686 | h686
              · rcases m.htr 1 2 4 (by decide) (by decide) with h687 | h687
                · linarith only [h0, h3, h680, h687, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h689 | h689
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h690 | h690
                    · linarith only [h0, h3, h681, h689, h690, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h692 | h692
                      · linarith only [h683, h690, h692, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h694 | h694
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h695 | h695
                          · linarith only [h2, h681, h695, hlam]
                          · linarith only [h0, h3, h689, h695, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi2]
                        · linarith only [h685, h687, h689, h694, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · linarith only [h3, h680, h689, hc12, hc24, hlam, hphi]
              · linarith only [h2, h683, h686, hc12, hlam, hphi, ht23, u3elo4]
            · linarith only [h3, h680, h685, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h702 | h702
        · linarith only [h2, h3, h702, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h704 | h704
          · linarith only [h702, h704, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h706 | h706
            · rcases m.htr 1 2 3 (by decide) (by decide) with h707 | h707
              · rcases m.htr 1 2 4 (by decide) (by decide) with h708 | h708
                · linarith only [h0, h3, h708, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h710 | h710
                  · linarith only [h0, h680, h710, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h712 | h712
                    · linarith only [h702, h712, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h714 | h714
                      · linarith only [h0, h680, h704, h707, h714, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h716 | h716
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h717 | h717
                          · linarith only [h0, h3, h707, h712, h717, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · linarith only [h2, h3, h717, hc23, hlam, hphi, u3elo3]
                        · linarith only [h702, h706, h707, h708, h716, hc23, hlam, hphi, u3elo3]
              · linarith only [h2, h3, h707, hc12, hc24, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h722 | h722
              · rcases m.htr 1 2 4 (by decide) (by decide) with h723 | h723
                · linarith only [h0, h3, h723, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h725 | h725
                  · linarith only [h0, h680, h725, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h727 | h727
                    · linarith only [h702, h727, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h729 | h729
                      · linarith only [h727, h729, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h731 | h731
                        · linarith only [h3, h706, h727, h731, hc02, hlam, hphi, ht23, u3elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h733 | h733
                          · linarith only [h2, h702, h733, hlam]
                          · linarith only [h0, h3, h722, h733, hc23, hlam, hphi, u3elo3]
              · linarith only [h2, h3, h722, hc12, hc24, hlam, hphi]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h737 | h737
    · rcases m.htr 0 2 5 (by decide) (by decide) with h738 | h738
      · linarith only [h2, h738, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h740 | h740
        · rcases m.htr 0 3 5 (by decide) (by decide) with h741 | h741
          · rcases m.htr 0 4 5 (by decide) (by decide) with h742 | h742
            · linarith only [h2, h737, h742, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h744 | h744
              · linarith only [h0, h2, h737, h744, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h746 | h746
                · rcases m.htr 1 2 5 (by decide) (by decide) with h747 | h747
                  · linarith only [h0, h738, h747, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h749 | h749
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h750 | h750
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h751 | h751
                        · linarith only [h0, h2, h742, h746, h751, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h753 | h753
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h754 | h754
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h755 | h755
                              · linarith only [h737, h738, h751, h754, h755, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h757 | h757
                                · linarith only [h738, h755, h757, hc02, hlam, hphi, ht23, u3elo3]
                                · rcases h0emin with h759 | h759 | h759 | h759 | h759
                                  · rcases h2bigk with h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [hlam, p760_0]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [h738, h746, h753, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p760_1]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [h2, hlam, p760_0]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [h2, h753, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p760_1, u3elo2]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [h738, hlam, p760_0]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [h0, hlam, p760_0]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [hlam, p760_0]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [h744, hlam, p760_0]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [h0, h2, h753, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p760_1, u3elo2]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [h747, hlam, p760_0]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [hc02, hlam, hphi, ht23, p760_1, u3elo2]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht23, p760_1, u3elo2]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [hlam, p760_0]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      rcases p760_3 (m.d 0 2) (by simp) with h774 | h774
                                      · linarith only [h2, h774, hlam]
                                      · linarith only [h737, h774, hlam]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p760_1, u3elo2, u5ehi2]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [h737, hlam, p760_0]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [h746, hlam, p760_0]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [h753, hlam, p760_1]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [hlam, p760_0]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [h755, hlam, p760_1]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [h0, h746, h753, h754, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p760_1, u3elo2]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [h746, h753, h754, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p760_1, u3elo2]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [h754, hlam, p760_1]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      rcases p760_3 (m.d 0 2) (by simp) with h786 | h786
                                      · linarith only [h738, h786, hlam]
                                      · linarith only [h737, h786, hlam]
                                    · have p760_0 := h760c.1
                                      have p760_1 := h760c.2.1
                                      have p760_2 := h760c.2.2.1
                                      have p760_3 := h760c.2.2.2
                                      linarith only [hlam, p760_0]
                                  · linarith only [h2, h759, hlam, ht01, ht12, ht23, u3elo2]
                                  · linarith only [h2, h759, hlam, ht01, ht12, ht23, u3elo2]
                                  · linarith only [h2, h737, h759, hlam, ht01, ht12, ht23, u3elo2]
                                  · linarith only [h2, h741, h759, hlam, ht01, ht12, ht23, u3elo2]
                            · linarith only [h2, h741, h754, hlam]
                          · linarith only [h2, h753, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h741, h749, h750, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                    · linarith only [h2, h740, h744, h746, h749, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h2, h737, h746, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h799 | h799
            · linarith only [h2, h737, h741, h799, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h801 | h801
              · linarith only [h0, h2, h741, h801, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h803 | h803
                · rcases m.htr 1 2 5 (by decide) (by decide) with h804 | h804
                  · linarith only [h0, h738, h804, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h806 | h806
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h807 | h807
                      · linarith only [h0, h2, h741, h803, h807, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h809 | h809
                        · linarith only [h0, h1, h2, h799, h803, h809, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h811 | h811
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h812 | h812
                            · linarith only [h2, h741, h812, hc02, hlam, hphi, ht23, u3elo2]
                            · linarith only [h0, h2, h803, h811, h812, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h0, h2, h803, h811, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h740, h806, hc13, hlam, hphi, u3elo0]
                · linarith only [h2, h737, h741, h803, hc12, hlam, hphi, ht23, u3elo4]
        · linarith only [h2, h737, h740, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h819 | h819
      · linarith only [h2, h819, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h821 | h821
        · rcases m.htr 0 3 5 (by decide) (by decide) with h822 | h822
          · rcases m.htr 0 4 5 (by decide) (by decide) with h823 | h823
            · rcases m.htr 1 2 3 (by decide) (by decide) with h824 | h824
              · linarith only [h0, h2, h822, h824, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h826 | h826
                · linarith only [h0, h737, h826, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h828 | h828
                  · linarith only [h0, h819, h828, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h830 | h830
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h831 | h831
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h832 | h832
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h833 | h833
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h834 | h834
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h835 | h835
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h836 | h836
                                · linarith only [h830, h836, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                                · rcases h0emin with h838 | h838 | h838 | h838 | h838
                                  · rcases h2bigk with h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [hlam, p839_0]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [h819, hc12, hc25, hlam, hphi, p839_1]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [h2, hlam, p839_0]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [h737, hlam, p839_0]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [h819, hlam, p839_0]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [h0, hlam, p839_0]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [hlam, p839_0]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [h824, hlam, p839_0]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [h826, hlam, p839_0]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [h828, hlam, p839_0]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [hc02, hlam, hphi, ht23, p839_1, u3elo2]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht23, p839_1, u3elo2]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [hlam, p839_0]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [h737, h823, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p839_1, u3elo2, u5ehi0]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p839_1, u3elo2, u5ehi2]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [h0, h833, hc12, hlam, hphi, ht23, p839_1, u3elo2]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [h833, hc12, hlam, hphi, ht23, p839_1, u3elo2]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [h833, hlam, p839_1]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [hlam, p839_0]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [h0, h819, h833, hc12, hlam, hphi, ht23, p839_1, u3elo2]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [h0, h834, hc12, hlam, hphi, ht23, p839_1, u3elo2]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [h834, hc12, hlam, hphi, ht23, p839_1, u3elo2]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [h834, hlam, p839_1]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [h835, hlam, p839_0]
                                    · have p839_0 := h839c.1
                                      have p839_1 := h839c.2.1
                                      have p839_2 := h839c.2.2.1
                                      have p839_3 := h839c.2.2.2
                                      linarith only [hlam, p839_0]
                                  · linarith only [h2, h838, hlam, ht01, ht12, ht23, u3elo2]
                                  · linarith only [h838, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h737, h833, h838, hlam, ht01, ht12, ht23, u3elo2]
                                  · linarith only [h819, h834, h838, hlam, ht01, ht12, ht23, u3elo2]
                              · linarith only [h1, h737, h823, h832, h835, hlam]
                            · linarith only [h2, h821, h823, h834, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                          · linarith only [h2, h821, h823, h833, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi4]
                        · linarith only [h821, h823, h826, h832, hc12, hlam, hphi, ht23, u3elo0]
                      · linarith only [h2, h822, h831, hc13, hlam, hphi, u3elo2]
                    · linarith only [h2, h821, h824, h830, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h875 | h875
              · linarith only [h0, h2, h822, h875, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h877 | h877
                · linarith only [h0, h737, h877, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h879 | h879
                  · linarith only [h0, h819, h879, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h881 | h881
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h882 | h882
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h883 | h883
                        · linarith only [h737, h823, h881, h883, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h885 | h885
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h886 | h886
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h887 | h887
                              · linarith only [h0, h737, h823, h885, h887, hc12, hlam, hphi, ht23, u3elo2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h889 | h889
                                · linarith only [h0, h737, h887, h889, hc12, hlam, hphi, ht23, u3elo3]
                                · rcases h0emin with h891 | h891 | h891 | h891 | h891
                                  · rcases h2bigk with h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [hlam, p892_0]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [h737, hc12, hc24, hlam, hphi, p892_1]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [h2, hlam, p892_0]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [h737, hlam, p892_0]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [h819, hlam, p892_0]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [h0, hlam, p892_0]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [hlam, p892_0]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [h875, hlam, p892_0]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [h877, hlam, p892_0]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [h879, hlam, p892_0]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [hc02, hlam, hphi, ht23, p892_1, u3elo2]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht23, p892_1, u3elo2]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [hlam, p892_0]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [h0, h737, hc12, hlam, hphi, ht23, p892_1, u3elo2]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p892_1, u3elo2, u5ehi2]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [h0, h885, hc12, hlam, hphi, ht23, p892_1, u3elo2]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [h885, hc12, hlam, hphi, ht23, p892_1, u3elo2]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [h885, hlam, p892_1]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [hlam, p892_0]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [h887, hlam, p892_1]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [h0, h886, hc12, hlam, hphi, ht23, p892_1, u3elo2]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [h886, hc12, hlam, hphi, ht23, p892_1, u3elo2]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [h886, hlam, p892_1]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [h0, h737, h886, hc12, hlam, hphi, ht23, p892_1, u3elo2]
                                    · have p892_0 := h892c.1
                                      have p892_1 := h892c.2.1
                                      have p892_2 := h892c.2.2.1
                                      have p892_3 := h892c.2.2.2
                                      linarith only [hlam, p892_0]
                                  · linarith only [h2, h891, hlam, ht01, ht12, ht23, u3elo2]
                                  · linarith only [h2, h891, hlam, ht01, ht12, ht23, u3elo2]
                                  · linarith only [h2, h822, h823, h891, hlam, ht01, ht12, ht23, u3elo2]
                                  · linarith only [h2, h822, h891, hlam, ht01, ht12, ht23, u3elo2]
                            · linarith only [h2, h822, h886, hlam]
                          · linarith only [h2, h821, h885, hlam]
                      · linarith only [h2, h822, h882, hc13, hlam, hphi, u3elo2]
                    · linarith only [h2, h821, h875, h881, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h926 | h926
            · linarith only [h821, h822, h926, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h928 | h928
              · linarith only [h0, h2, h928, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h930 | h930
                · linarith only [h0, h737, h930, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h932 | h932
                  · linarith only [h0, h737, h821, h822, h932, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h934 | h934
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h935 | h935
                      · linarith only [h737, h821, h822, h935, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h937 | h937
                        · linarith only [h926, h934, h935, h937, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h939 | h939
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h940 | h940
                            · linarith only [h935, h940, hc13, hlam, hphi, u3elo2]
                            · linarith only [h2, h940, hc02, hlam, hphi, ht23, u3elo4]
                          · linarith only [h0, h2, h939, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h821, h822, h934, hc13, hlam, hphi, u3elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h945 | h945
          · linarith only [h821, h945, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h947 | h947
            · rcases m.htr 1 2 3 (by decide) (by decide) with h948 | h948
              · linarith only [h0, h2, h948, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h950 | h950
                · linarith only [h0, h737, h950, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h952 | h952
                  · linarith only [h0, h819, h952, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h954 | h954
                    · linarith only [h2, h821, h954, hc02, hlam, hphi, ht23, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h956 | h956
                      · linarith only [h0, h2, h945, h954, h956, hc12, hlam, hphi, ht23, u3elo3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h958 | h958
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h959 | h959
                          · linarith only [h954, h959, hc13, hlam, hphi, u3elo2]
                          · linarith only [h0, h2, h959, hc12, hlam, hphi, ht23, u3elo3]
                        · linarith only [h821, h947, h950, h958, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h963 | h963
              · linarith only [h0, h2, h963, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h965 | h965
                · linarith only [h0, h737, h965, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h967 | h967
                  · linarith only [h0, h2, h819, h967, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h969 | h969
                    · linarith only [h2, h821, h969, hc02, hlam, hphi, ht23, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h971 | h971
                      · linarith only [h969, h971, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h973 | h973
                        · linarith only [h0, h2, h821, h947, h969, h973, hc12, hlam, hphi, ht23, u3elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h975 | h975
                          · linarith only [h969, h975, hc13, hlam, hphi, u3elo2]
                          · linarith only [h0, h2, h975, hc12, hlam, hphi, ht23, u3elo3]

end R2N4
