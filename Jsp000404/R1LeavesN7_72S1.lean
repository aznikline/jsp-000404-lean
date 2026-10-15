import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_R_L_R_L_R_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h13, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                              · linarith only [h0, h13, h15, h3, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                              · linarith only [h0, h11, h15, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                            · linarith only [h0, h18, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                              · linarith only [h0, h20, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                              · linarith only [h0, h11, h20, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                            · linarith only [h0, h24, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                              · linarith only [h24, h26, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
                                  · rcases h5bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h0, h10, h3, h5, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi4]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h0, h3, h5, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi4]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h0, h3, h5, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p30_1, u3ehi4]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      rcases p30_3 (m.d 0 5) (by simp) with h35 | h35
                                      · rcases p30_3 (m.d 1 5) (by simp) with h36 | h36
                                        · linarith only [h2, h36, hlam]
                                        · linarith only [h23, h36, hlam]
                                      · linarith only [h35, h7, hlam]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h2, hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h26, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi2]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h11, hlam, p30_1]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p30_1]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h4, hlam, p30_1]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h10, hlam, p30_1]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h26, hlam, p30_1]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h0, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p30_1]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h6, hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h0, h3, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p30_1]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h0, h3, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p30_1]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h0, h29, h3, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p30_1]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h7, hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h23, hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h28, hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h29, hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [hlam, p30_0]
                                  · linarith only [h0, h23, h29, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h0, h23, h28, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h62 | h62
                            · linarith only [h0, h62, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h64 | h64
                              · linarith only [h0, h11, h23, h3, h5, h62, h64, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h66 | h66
                                · linarith only [h23, h66, h9, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h68 | h68
                                  · linarith only [h23, h62, h68, h9, hc34, hlam, hphi, u3ehi2]
                                  · linarith only [h0, h3, h5, h62, h68, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h10, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h8, h9, hc24, hlam, hphi, u2ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
                    · linarith only [h73, h8, hc23, hlam, hphi, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
                      · linarith only [h0, h3, h75, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h77 | h77
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h78 | h78
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h80 | h80
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h81 | h81
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h82 | h82
                                  · rcases h5bigk with h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [hlam, p83_0]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h0, h3, h5, h7, h75, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi1]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h0, h3, h5, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h0, h3, h5, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p83_1, u3ehi4]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      rcases p83_3 (m.d 0 5) (by simp) with h88 | h88
                                      · rcases p83_3 (m.d 1 5) (by simp) with h89 | h89
                                        · linarith only [h2, h89, hlam]
                                        · linarith only [h78, h89, hlam]
                                      · linarith only [h7, h88, hlam]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h2, hlam, p83_0]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [hlam, p83_0]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h75, hlam, p83_0]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p83_1, u3ehi4]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p83_1]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h4, hlam, p83_1]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h0, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p83_1]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [hlam, p83_0]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h0, h3, h80, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p83_1, u3ehi4]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h0, h3, h79, h81, hc01, hc45, hlam, hphi, ht0b, ht5b, p83_1]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h6, hlam, p83_0]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h77, hlam, p83_0]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h80, hlam, p83_0]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [hlam, p83_0]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h0, h3, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p83_1]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h7, hlam, p83_0]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h78, hlam, p83_0]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h81, hlam, p83_0]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [h82, hlam, p83_0]
                                    · have p83_0 := h83c.1
                                      have p83_1 := h83c.2.1
                                      have p83_2 := h83c.2.2.1
                                      have p83_3 := h83c.2.2.2
                                      linarith only [hlam, p83_0]
                                  · linarith only [h0, h3, h73, h78, h79, h82, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h73, h78, h81, hlam]
                              · linarith only [h77, h8, h80, hlam]
                            · linarith only [h77, h79, h8, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h119 | h119
                                · linarith only [h119, h73, h78, hc24, hlam, hphi, u2ehi1]
                                · linarith only [h0, h119, h3, h5, h7, h73, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h117, h118, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h117, h8, hc34, hlam, hphi, ht23, u2ehi1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h124 | h124
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h126 | h126
                              · linarith only [h0, h126, h3, h77, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · linarith only [h125, h126, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h125, h8, hc34, hlam, hphi, ht23, u2ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h130 | h130
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h131 | h131
                              · linarith only [h131, h77, h8, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h130, h131, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h130, h8, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h137 | h137
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h138 | h138
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h139 | h139
                          · linarith only [h139, h7, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                            · linarith only [h0, h135, h141, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h141, h5, h7, hc45, hlam, hphi, ht34, u3ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h144 | h144
                          · linarith only [h144, h7, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h146 | h146
                            · linarith only [h0, h135, h146, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h146, h5, h7, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h0, h135, h137, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h135, h136, hc24, hlam, hphi, u2ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h151 | h151
                    · linarith only [h135, h151, hc23, hlam, hphi, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h153 | h153
                      · linarith only [h0, h135, h153, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h155 | h155
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h156 | h156
                          · linarith only [h156, h7, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h158 | h158
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h159 | h159
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h160 | h160
                                · linarith only [h0, h158, h160, h3, h7, hc01, hlam, hphi, u0ehi3]
                                · linarith only [h151, h160, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                              · linarith only [h151, h155, h158, h159, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · linarith only [h158, h5, h7, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h165 | h165
                          · linarith only [h165, h7, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h167 | h167
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h168 | h168
                              · linarith only [h135, h155, h168, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h0, h167, h168, h3, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h135, h167, hc34, hlam, hphi, ht23, u2ehi1]
              · linarith only [h5, h6, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h173 | h173
              · linarith only [h173, h5, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h175 | h175
                · rcases m.htr 1 2 3 (by decide) (by decide) with h176 | h176
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h177 | h177
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h178 | h178
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h179 | h179
                        · linarith only [h173, h179, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h181 | h181
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h182 | h182
                            · linarith only [h1, h173, h176, h182, hc35, hlam, hphi, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h184 | h184
                              · linarith only [h0, h173, h177, h182, h184, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h186 | h186
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h187 | h187
                                  · rcases h5bigk with h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [hlam, p188_0]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [h175, h176, h179, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p188_1, u2ehi2]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [h175, h5, hc34, hlam, hphi, ht23, p188_1, u2ehi4]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [h173, hlam, p188_1]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      rcases p188_3 (m.d 0 5) (by simp) with h193 | h193
                                      · rcases p188_3 (m.d 1 5) (by simp) with h194 | h194
                                        · linarith only [h194, h2, hlam]
                                        · linarith only [h181, h194, hlam]
                                      · linarith only [h175, h193, hlam]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [h2, hlam, p188_0]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [hlam, p188_0]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [h181, h184, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p188_1, u2ehi2]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [h179, hlam, p188_1]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [h0, h177, h181, hc01, hc45, hlam, hphi, ht0b, ht5b, p188_1]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [h4, hlam, p188_1]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [h178, hlam, p188_1]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [hlam, p188_0]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [h184, hlam, p188_1]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [h0, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p188_1]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p188_1, u0ehi4]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [h178, hc35, hlam, hphi, ht23, p188_1, u2ehi4]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht23, p188_1, u2ehi4]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [hlam, p188_0]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      rcases p188_3 (m.d 0 5) (by simp) with h212 | h212
                                      · linarith only [h173, h212, hlam]
                                      · linarith only [h175, h212, hlam]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [h175, hlam, p188_0]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [h181, hlam, p188_0]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [h186, hlam, p188_0]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [h187, hlam, p188_0]
                                    · have p188_0 := h188c.1
                                      have p188_1 := h188c.2.1
                                      have p188_2 := h188c.2.2.1
                                      have p188_3 := h188c.2.2.2
                                      linarith only [hlam, p188_0]
                                  · linarith only [h0, h177, h184, h186, h187, h5, hc01, hc45, hlam, hphi, ht23, ht34, u0ehi2, u2ehi2]
                                · linarith only [h0, h177, h181, h186, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h175, h177, h181, h5, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h176, h178, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h176, h177, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h176, h3, h5, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h226 | h226
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h227 | h227
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h228 | h228
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h229 | h229
                        · linarith only [h1, h175, h229, h5, hc45, hlam, hphi, ht34, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h231 | h231
                          · linarith only [h175, h231, h5, hc14, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h233 | h233
                            · linarith only [h1, h173, h226, h233, hc35, hlam, hphi, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h235 | h235
                              · linarith only [h0, h173, h227, h233, h235, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h237 | h237
                                · linarith only [h175, h227, h237, h5, hc14, hlam, hphi, ht01, u0ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h239 | h239
                                  · linarith only [h175, h239, h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                                  · linarith only [h0, h228, h233, h237, h239, h5, hc01, hc45, hlam, hphi, ht23, ht34, u0ehi2, u2ehi2]
                      · linarith only [h0, h226, h228, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h226, h227, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h226, h3, h5, hc34, hlam, hphi, ht23, u2ehi1]
          · linarith only [h3, h4, hc25, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h246 | h246
          · linarith only [h246, h3, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h248 | h248
            · rcases m.htr 0 3 5 (by decide) (by decide) with h249 | h249
              · rcases m.htr 0 4 5 (by decide) (by decide) with h250 | h250
                · rcases m.htr 1 2 3 (by decide) (by decide) with h251 | h251
                  · linarith only [h251, h3, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h253 | h253
                    · linarith only [h0, h253, h3, hc23, hlam, hphi, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h255 | h255
                      · linarith only [h0, h246, h255, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h257 | h257
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h258 | h258
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h259 | h259
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h260 | h260
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h261 | h261
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h262 | h262
                                  · rcases h5bigk with h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [hlam, p263_0]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h248, h250, h255, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p263_1, u2ehi1]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h246, hlam, p263_0]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h248, h250, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p263_1, u3ehi4]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      rcases p263_3 (m.d 0 5) (by simp) with h268 | h268
                                      · rcases p263_3 (m.d 1 5) (by simp) with h269 | h269
                                        · linarith only [h2, h269, hlam]
                                        · linarith only [h258, h269, hlam]
                                      · linarith only [h250, h268, hlam]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h2, hlam, p263_0]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [hlam, p263_0]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h255, hlam, p263_0]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h258, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p263_1, u3ehi4]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h1, h257, hc01, hc45, hlam, hphi, ht0b, ht5b, p263_1]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h259, h261, hc23, hlam, hphi, ht01, ht12, p263_1, u0ehi4]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h255, h259, h261, hc23, hlam, hphi, p263_1, u2ehi1]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [hlam, p263_0]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h259, h261, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p263_1, u3ehi4]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      rcases p263_3 (m.d 0 5) (by simp) with h282 | h282
                                      · linarith only [h246, h282, hlam]
                                      · linarith only [h250, h282, hlam]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h249, hlam, p263_0]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h257, hlam, p263_0]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h260, hlam, p263_0]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [hlam, p263_0]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h249, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p263_1]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h250, hlam, p263_0]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h258, hlam, p263_0]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h261, hlam, p263_0]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [h262, hlam, p263_0]
                                    · have p263_0 := h263c.1
                                      have p263_1 := h263c.2.1
                                      have p263_2 := h263c.2.2.1
                                      have p263_3 := h263c.2.2.2
                                      linarith only [hlam, p263_0]
                                  · rcases h5bigk with h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [hlam, p295_0]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h258, h262, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p295_1, u3ehi3]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h246, hlam, p295_0]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h246, h259, h261, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p295_1, u3ehi4]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h246, h259, h261, h262, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p295_1, u3ehi3]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h2, hlam, p295_0]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [hlam, p295_0]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h255, hlam, p295_0]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p295_1, u3ehi4]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h1, h257, h262, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p295_1, u3ehi3]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h259, h261, hc23, hlam, hphi, ht01, ht12, p295_1, u0ehi4]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h255, h259, h261, hc23, hlam, hphi, p295_1, u2ehi1]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [hlam, p295_0]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h259, h261, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p295_1, u3ehi4]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h259, h261, h262, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p295_1, u3ehi3]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h249, hlam, p295_0]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h257, hlam, p295_0]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h260, hlam, p295_0]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [hlam, p295_0]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h262, hlam, p295_1]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h250, hlam, p295_0]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h258, hlam, p295_0]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h261, hlam, p295_0]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [h2, h258, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p295_1, u3ehi4]
                                    · have p295_0 := h295c.1
                                      have p295_1 := h295c.2.1
                                      have p295_2 := h295c.2.2.1
                                      have p295_3 := h295c.2.2.2
                                      linarith only [hlam, p295_0]
                                · linarith only [h248, h250, h261, h3, hc23, hlam, hphi, u2ehi3]
                              · linarith only [h260, h3, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                            · linarith only [h259, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · linarith only [h248, h250, h253, h258, h3, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h249, h251, h257, h3, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h326 | h326
                  · linarith only [h3, h326, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h328 | h328
                    · linarith only [h0, h3, h328, hc23, hlam, hphi, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h330 | h330
                      · linarith only [h0, h246, h330, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h332 | h332
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h333 | h333
                          · linarith only [h250, h333, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h335 | h335
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h336 | h336
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h337 | h337
                                · linarith only [h250, h335, h337, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                                · linarith only [h328, h337, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                              · linarith only [h1, h332, h336, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h1, h3, h332, h335, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h249, h3, h326, h332, hc23, hlam, hphi, u2ehi1]
              · linarith only [h248, h249, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h344 | h344
              · linarith only [h248, h344, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h346 | h346
                · rcases m.htr 1 2 3 (by decide) (by decide) with h347 | h347
                  · linarith only [h0, h3, h347, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h349 | h349
                    · linarith only [h0, h248, h3, h349, hc34, hlam, hphi, ht23, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h351 | h351
                      · linarith only [h0, h248, h3, h351, hc34, hlam, hphi, ht23, u2ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h353 | h353
                        · linarith only [h1, h3, h344, h353, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h355 | h355
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h356 | h356
                            · linarith only [h248, h3, h356, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                            · linarith only [h3, h356, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · linarith only [h248, h346, h349, h355, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h360 | h360
                  · linarith only [h3, h360, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h362 | h362
                    · linarith only [h0, h3, h362, hc23, hlam, hphi, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h364 | h364
                      · linarith only [h0, h246, h248, h3, h346, h364, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h366 | h366
                        · linarith only [h3, h344, h366, hc13, hlam, hphi, ht01, u0ehi1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h368 | h368
                          · linarith only [h248, h3, h346, h368, hc14, hlam, hphi, ht01, u0ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h370 | h370
                            · linarith only [h248, h3, h370, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                            · linarith only [h3, h370, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h373 | h373
        · rcases m.htr 0 2 5 (by decide) (by decide) with h374 | h374
          · linarith only [h0, h2, h374, hlam]
          · linarith only [h373, h374, hc25, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h377 | h377
          · linarith only [h373, h377, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h379 | h379
            · rcases m.htr 0 3 5 (by decide) (by decide) with h380 | h380
              · linarith only [h1, h2, h380, hlam]
              · linarith only [h379, h380, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h383 | h383
              · linarith only [h379, h383, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h385 | h385
                · rcases m.htr 1 2 3 (by decide) (by decide) with h386 | h386
                  · linarith only [h0, h2, h373, h386, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h388 | h388
                    · linarith only [h1, h2, h386, h388, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h390 | h390
                      · linarith only [h1, h2, h377, h386, h390, hc15, hlam, hphi, ht01, u0ehi1]
                      · linarith only [h1, h2, h386, h390, hc25, hlam, hphi, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h393 | h393
                  · linarith only [h0, h373, h393, hc01, hlam, hphi, u0ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h395 | h395
                    · linarith only [h1, h2, h393, h395, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h397 | h397
                      · linarith only [h1, h2, h373, h379, h385, h393, h397, hc15, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi1, u2ehi4]
                      · linarith only [h1, h2, h393, h397, hc25, hlam, hphi, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h400 | h400
      · rcases m.htr 0 2 3 (by decide) (by decide) with h401 | h401
        · linarith only [h0, h1, h401, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h403 | h403
          · linarith only [h401, h403, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h405 | h405
            · rcases m.htr 0 3 5 (by decide) (by decide) with h406 | h406
              · rcases m.htr 0 4 5 (by decide) (by decide) with h407 | h407
                · rcases m.htr 1 2 3 (by decide) (by decide) with h408 | h408
                  · linarith only [h401, h408, hc12, hlam, hphi, ht01, u0ehi1]
                  · linarith only [h0, h1, h408, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h411 | h411
                  · linarith only [h0, h1, h411, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1, h411, hc23, hlam, hphi, u2ehi1]
              · linarith only [h0, h1, h406, hc35, hlam, hphi, ht23, u2ehi1]
            · linarith only [h0, h1, h405, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h416 | h416
        · linarith only [h0, h1, h416, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h418 | h418
          · linarith only [h416, h418, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h420 | h420
            · rcases m.htr 0 3 5 (by decide) (by decide) with h421 | h421
              · rcases m.htr 0 4 5 (by decide) (by decide) with h422 | h422
                · rcases m.htr 1 2 3 (by decide) (by decide) with h423 | h423
                  · linarith only [h416, h423, hc12, hlam, hphi, ht01, u0ehi1]
                  · linarith only [h0, h1, h423, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h426 | h426
                  · linarith only [h0, h1, h426, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1, h426, hc23, hlam, hphi, u2ehi1]
              · linarith only [h0, h1, h421, hc35, hlam, hphi, ht23, u2ehi1]
            · linarith only [h0, h1, h420, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h431 | h431
    · rcases m.htr 0 1 5 (by decide) (by decide) with h432 | h432
      · rcases m.htr 0 2 3 (by decide) (by decide) with h433 | h433
        · rcases m.htr 0 2 5 (by decide) (by decide) with h434 | h434
          · rcases m.htr 0 3 4 (by decide) (by decide) with h435 | h435
            · rcases m.htr 0 3 5 (by decide) (by decide) with h436 | h436
              · rcases m.htr 0 4 5 (by decide) (by decide) with h437 | h437
                · rcases m.htr 1 2 3 (by decide) (by decide) with h438 | h438
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h439 | h439
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h440 | h440
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h441 | h441
                        · linarith only [h0, h431, h441, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h0, h431, h436, h438, h441, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h440, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                    · linarith only [h0, h439, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                  · linarith only [h0, h431, h435, h438, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h447 | h447
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h448 | h448
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h449 | h449
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h450 | h450
                        · linarith only [h0, h431, h450, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h0, h431, h436, h447, h450, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h449, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                    · linarith only [h0, h431, h447, h448, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h431, h447, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h435, h436, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h457 | h457
              · linarith only [h435, h457, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h459 | h459
                · rcases m.htr 1 2 3 (by decide) (by decide) with h460 | h460
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h461 | h461
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h462 | h462
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h463 | h463
                        · linarith only [h457, h463, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h465 | h465
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h466 | h466
                            · linarith only [h0, h432, h460, h463, h466, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h468 | h468
                              · linarith only [h0, h432, h457, h460, h463, h468, hc12, hlam, hphi, ht01, u0ehi2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h470 | h470
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h471 | h471
                                  · rcases h5bigk with h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [hlam, p472_0]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [h459, h460, h463, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p472_1, u2ehi2]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [h0, h432, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p472_1]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [h457, hlam, p472_1]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [h0, h432, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p472_1]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [h432, hlam, p472_0]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [hlam, p472_0]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [h0, h432, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p472_1, u2ehi4]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [h463, hlam, p472_1]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [h0, h432, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p472_1]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [h434, hlam, p472_1]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [h462, hlam, p472_1]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [hlam, p472_0]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [h468, hlam, p472_1]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [h0, h434, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p472_1]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p472_1, u0ehi4]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [h460, h463, hc35, hlam, hphi, ht23, p472_1, u2ehi2]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht23, p472_1, u2ehi4]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [hlam, p472_0]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      rcases p472_3 (m.d 0 5) (by simp) with h492 | h492
                                      · linarith only [h457, h492, hlam]
                                      · linarith only [h459, h492, hlam]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [h459, hlam, p472_0]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [h465, hlam, p472_0]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [h470, hlam, p472_0]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [h471, hlam, p472_0]
                                    · have p472_0 := h472c.1
                                      have p472_1 := h472c.2.1
                                      have p472_2 := h472c.2.2.1
                                      have p472_3 := h472c.2.2.2
                                      linarith only [hlam, p472_0]
                                  · linarith only [h0, h432, h435, h460, h463, h471, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi2, u2ehi2]
                                · linarith only [h0, h432, h465, h470, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h435, h459, h461, h465, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h0, h462, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                    · linarith only [h0, h431, h460, h461, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h431, h460, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h506 | h506
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h507 | h507
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h508 | h508
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h509 | h509
                        · linarith only [h0, h431, h509, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h511 | h511
                          · linarith only [h435, h459, h511, hc14, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h513 | h513
                            · linarith only [h0, h432, h506, h509, h513, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h515 | h515
                              · linarith only [h0, h432, h457, h507, h511, h513, h515, hc12, hlam, hphi, ht01, u0ehi2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h517 | h517
                                · linarith only [h0, h432, h435, h459, h507, h511, h517, hc12, hlam, hphi, ht01, u0ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h519 | h519
                                  · linarith only [h0, h432, h435, h459, h507, h511, h513, h519, hc12, hc34, hlam, hphi, ht01, ht23, u0ehi2, u2ehi2]
                                  · linarith only [h0, h432, h435, h507, h511, h513, h519, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi2, u2ehi2]
                      · linarith only [h0, h508, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                    · linarith only [h0, h431, h506, h507, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h431, h506, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h433, h434, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h431, h433, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h527 | h527
        · rcases m.htr 0 2 5 (by decide) (by decide) with h528 | h528
          · rcases m.htr 0 3 4 (by decide) (by decide) with h529 | h529
            · rcases m.htr 0 3 5 (by decide) (by decide) with h530 | h530
              · linarith only [h431, h432, h530, hlam]
              · linarith only [h529, h530, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h533 | h533
              · linarith only [h529, h533, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h535 | h535
                · rcases m.htr 1 2 3 (by decide) (by decide) with h536 | h536
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h537 | h537
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h538 | h538
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h539 | h539
                        · linarith only [h431, h533, h539, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h431, h432, h536, h539, hc35, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h528, h537, h538, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h0, h528, h537, hc24, hlam, hphi, u2ehi4]
                  · linarith only [h0, h431, h536, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h545 | h545
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h546 | h546
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h547 | h547
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h548 | h548
                        · linarith only [h431, h432, h547, h548, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h431, h432, h545, h548, hc35, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h546, h547, hc25, hlam, hphi, u2ehi3]
                    · linarith only [h0, h431, h545, h546, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h431, h545, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h527, h528, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h431, h527, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h556 | h556
      · rcases m.htr 0 2 3 (by decide) (by decide) with h557 | h557
        · rcases m.htr 0 2 5 (by decide) (by decide) with h558 | h558
          · rcases m.htr 0 3 4 (by decide) (by decide) with h559 | h559
            · rcases m.htr 0 3 5 (by decide) (by decide) with h560 | h560
              · rcases m.htr 0 4 5 (by decide) (by decide) with h561 | h561
                · rcases m.htr 1 2 3 (by decide) (by decide) with h562 | h562
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h563 | h563
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h564 | h564
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h565 | h565
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h566 | h566
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h567 | h567
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h568 | h568
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h569 | h569
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h570 | h570
                                  · rcases h5bigk with h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [hlam, p571_0]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h431, h556, h562, h564, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p571_1, u2ehi4]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h431, h556, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p571_1, u2ehi4]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h431, h556, h562, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p571_1, u3ehi4]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h431, h556, h562, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p571_1]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h556, hlam, p571_0]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [hlam, p571_0]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p571_1, u2ehi4]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h431, h556, h562, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p571_1, u3ehi4]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h431, h556, h562, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p571_1]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h558, hlam, p571_1]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h564, hlam, p571_1]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [hlam, p571_0]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p571_1, u3ehi4]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h431, h556, h562, h564, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p571_1]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h560, hlam, p571_0]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h565, hlam, p571_0]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h568, hlam, p571_0]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [hlam, p571_0]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h431, h556, h562, h564, h567, h570, hc12, hc23, hc45, hlam, hphi, ht01, ht0b, ht5b, p571_1, u2ehi4]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h561, hlam, p571_0]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h566, hlam, p571_0]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h569, hlam, p571_0]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [h570, hlam, p571_0]
                                    · have p571_0 := h571c.1
                                      have p571_1 := h571c.2.1
                                      have p571_2 := h571c.2.2.1
                                      have p571_3 := h571c.2.2.2
                                      linarith only [hlam, p571_0]
                                  · linarith only [h431, h556, h562, h566, h570, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h431, h556, h562, h566, h569, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h431, h556, h562, h565, h568, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h600 | h600
                              · linarith only [h567, h600, hc34, hlam, hphi, u3ehi4]
                              · linarith only [h431, h556, h562, h565, h600, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h603 | h603
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h604 | h604
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h605 | h605
                                · linarith only [h563, h566, h605, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h607 | h607
                                  · linarith only [h563, h566, h603, h607, hc23, hlam, hphi, u2ehi3]
                                  · rcases h5bigk with h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [hlam, p609_0]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h431, h556, h562, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p609_1]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h431, h556, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p609_1, u2ehi4]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h431, h556, h562, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p609_1, u3ehi4]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h431, h556, h562, h563, h566, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p609_1, u2ehi3]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h556, hlam, p609_0]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [hlam, p609_0]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p609_1, u2ehi4]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h431, h556, h562, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p609_1, u3ehi4]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h566, hlam, p609_1]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h558, hlam, p609_1]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h564, hlam, p609_1]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [hlam, p609_0]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p609_1, u3ehi4]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h605, hlam, p609_1]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h560, hlam, p609_0]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h565, hlam, p609_0]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h604, hlam, p609_0]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [hlam, p609_0]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h607, hlam, p609_1]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h561, hlam, p609_0]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h431, h559, h561, h562, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p609_1]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h431, h559, h561, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p609_1, u2ehi4]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [h431, h559, h561, h562, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p609_1, u3ehi4]
                                    · have p609_0 := h609c.1
                                      have p609_1 := h609c.2.1
                                      have p609_2 := h609c.2.2.1
                                      have p609_3 := h609c.2.2.2
                                      linarith only [hlam, p609_0]
                              · linarith only [h431, h556, h562, h565, h604, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h636 | h636
                              · linarith only [h603, h636, hc34, hlam, hphi, u3ehi4]
                              · linarith only [h431, h556, h562, h565, h636, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h431, h565, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                      · linarith only [h431, h556, h558, h562, h564, hlam]
                    · linarith only [h431, h556, h562, h563, hc24, hlam, hphi, ht01, ht12, u0ehi4]
                  · linarith only [h0, h557, h562, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h643 | h643
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h644 | h644
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h645 | h645
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h646 | h646
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h647 | h647
                          · linarith only [h561, h647, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h649 | h649
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h650 | h650
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h651 | h651
                                · linarith only [h556, h561, h644, h647, h651, hc01, hlam, hphi, u0ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h653 | h653
                                  · linarith only [h561, h653, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                                  · rcases h5bigk with h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [hlam, p655_0]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [h431, h556, h643, h644, h647, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p655_1, u2ehi3]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [h431, h556, h643, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p655_1]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [h431, h556, h643, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p655_1, u3ehi4]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [h561, hlam, p655_1]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [h556, hlam, p655_0]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [hlam, p655_0]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p655_1, u2ehi4]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [h431, h556, h643, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p655_1, u3ehi4]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [h647, hlam, p655_1]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [h558, hlam, p655_1]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [h645, hlam, p655_1]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [hlam, p655_0]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p655_1, u3ehi4]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [h651, hlam, p655_1]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [h560, hlam, p655_0]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [h646, hlam, p655_0]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [h650, hlam, p655_0]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [hlam, p655_0]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [h653, hlam, p655_1]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p655_1, u0ehi4]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [h645, hc45, hlam, hphi, ht23, ht34, p655_1, u2ehi4]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht23, ht34, p655_1, u2ehi4]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht34, p655_1, u3ehi4]
                                    · have p655_0 := h655c.1
                                      have p655_1 := h655c.2.1
                                      have p655_2 := h655c.2.2.1
                                      have p655_3 := h655c.2.2.2
                                      linarith only [hlam, p655_0]
                              · linarith only [h431, h556, h643, h646, h650, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h559, h561, h649, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h431, h646, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                      · linarith only [h0, h556, h561, h645, hc25, hlam, hphi, ht01, ht12, u0ehi3]
                    · linarith only [h0, h556, h561, h644, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                  · linarith only [h0, h556, h557, h561, h643, hc02, hlam, hphi, u0ehi3]
              · linarith only [h559, h560, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h688 | h688
              · linarith only [h559, h688, hc34, hlam, hphi, u3ehi4]
              · linarith only [h431, h556, h688, hlam]
          · linarith only [h557, h558, hc25, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h692 | h692
          · linarith only [h557, h692, hc23, hlam, hphi, u2ehi4]
          · linarith only [h0, h556, h692, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h695 | h695
        · rcases m.htr 0 2 5 (by decide) (by decide) with h696 | h696
          · rcases m.htr 0 3 4 (by decide) (by decide) with h697 | h697
            · rcases m.htr 0 3 5 (by decide) (by decide) with h698 | h698
              · rcases m.htr 0 4 5 (by decide) (by decide) with h699 | h699
                · rcases m.htr 1 2 3 (by decide) (by decide) with h700 | h700
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h701 | h701
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h702 | h702
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h703 | h703
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h704 | h704
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h705 | h705
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h706 | h706
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h707 | h707
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h708 | h708
                                  · rcases h5bigk with h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h556, hlam, p709_1]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h697, h699, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p709_1, u2ehi4]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h431, h697, h699, h700, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p709_1, u3ehi4]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      rcases p709_3 (m.d 0 5) (by simp) with h714 | h714
                                      · rcases p709_3 (m.d 1 5) (by simp) with h715 | h715
                                        · rcases p709_3 (m.d 2 5) (by simp) with h716 | h716
                                          · linarith only [h696, h716, hlam]
                                          · linarith only [h707, h716, hlam]
                                        · linarith only [h704, h715, hlam]
                                      · linarith only [h699, h714, hlam]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h700, h703, hc12, hlam, hphi, ht01, p709_1, u0ehi4]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h700, h703, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p709_1, u2ehi4]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h700, h703, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p709_1, u3ehi4]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      rcases p709_3 (m.d 0 5) (by simp) with h725 | h725
                                      · linarith only [h556, h725, hlam]
                                      · linarith only [h699, h725, hlam]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h696, hlam, p709_1]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h702, hlam, p709_1]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p709_1, u3ehi4]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h0, h695, h705, h707, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p709_1]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h698, hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h703, hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h706, hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h431, h697, h700, h708, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p709_1]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h699, hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h704, hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h707, hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h708, hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [hlam, p709_0]
                                  · linarith only [h0, h695, h705, h707, h708, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h744 | h744
                                  · linarith only [h707, h744, hc34, hlam, hphi, ht23, u2ehi3]
                                  · rcases h5bigk with h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [hlam, p746_0]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h556, hlam, p746_1]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p746_1, u2ehi4]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h556, h700, h703, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p746_1, u3ehi4]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h431, h697, h699, h700, h707, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p746_1, u2ehi3]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h700, h703, hc12, hlam, hphi, ht01, p746_1, u0ehi4]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [hlam, p746_0]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h700, h703, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p746_1, u2ehi4]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h700, h703, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p746_1, u3ehi4]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h700, h703, h707, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p746_1, u2ehi3]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h696, hlam, p746_1]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h702, hlam, p746_1]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [hlam, p746_0]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p746_1, u3ehi4]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h707, hlam, p746_1]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h698, hlam, p746_0]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h703, hlam, p746_0]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h706, hlam, p746_0]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [hlam, p746_0]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h744, hlam, p746_1]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h699, hlam, p746_0]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h704, hlam, p746_0]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h431, h697, h699, h700, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p746_1]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [h431, h697, h699, h700, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p746_1, u3ehi4]
                                    · have p746_0 := h746c.1
                                      have p746_1 := h746c.2.1
                                      have p746_2 := h746c.2.2.1
                                      have p746_3 := h746c.2.2.2
                                      linarith only [hlam, p746_0]
                              · linarith only [h431, h698, h700, h705, h706, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h773 | h773
                              · linarith only [h705, h773, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h775 | h775
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h776 | h776
                                  · rcases h5bigk with h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [hlam, p777_0]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [h556, hlam, p777_1]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p777_1, u2ehi4]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [h556, h700, h703, h773, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p777_1, u3ehi2]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      rcases p777_3 (m.d 0 5) (by simp) with h782 | h782
                                      · rcases p777_3 (m.d 1 5) (by simp) with h783 | h783
                                        · rcases p777_3 (m.d 2 5) (by simp) with h784 | h784
                                          · linarith only [h696, h784, hlam]
                                          · linarith only [h775, h784, hlam]
                                        · linarith only [h704, h783, hlam]
                                      · linarith only [h699, h782, hlam]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [h700, h703, hc12, hlam, hphi, ht01, p777_1, u0ehi4]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [hlam, p777_0]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [h700, h703, h773, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p777_1, u2ehi2]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [h700, h703, h773, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p777_1, u2ehi2]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      rcases p777_3 (m.d 0 5) (by simp) with h793 | h793
                                      · linarith only [h556, h793, hlam]
                                      · linarith only [h699, h793, hlam]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [h696, hlam, p777_1]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [h702, hlam, p777_1]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [hlam, p777_0]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [h773, hlam, p777_1]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [h0, h696, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p777_1]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [h698, hlam, p777_0]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [h703, hlam, p777_0]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht23, p777_1, u2ehi4]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [hlam, p777_0]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [h0, h695, h697, h776, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p777_1]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [h699, hlam, p777_0]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [h704, hlam, p777_0]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [h775, hlam, p777_0]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [h776, hlam, p777_0]
                                    · have p777_0 := h777c.1
                                      have p777_1 := h777c.2.1
                                      have p777_2 := h777c.2.2.1
                                      have p777_3 := h777c.2.2.2
                                      linarith only [hlam, p777_0]
                                  · linarith only [h0, h695, h697, h699, h705, h776, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h812 | h812
                                  · linarith only [h0, h695, h697, h705, h775, h812, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                  · linarith only [h704, h705, h812, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h0, h556, h695, h697, h699, h704, hc12, hlam, hphi, ht01, u0ehi0]
                        · linarith only [h431, h698, h703, hlam]
                      · linarith only [h0, h702, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                    · linarith only [h431, h700, h701, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                  · linarith only [h0, h695, h700, hc02, hlam, hphi, u0ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h820 | h820
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h821 | h821
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h822 | h822
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h823 | h823
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h824 | h824
                          · linarith only [h699, h824, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h826 | h826
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h827 | h827
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h828 | h828
                                · linarith only [h821, h824, h828, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h830 | h830
                                  · linarith only [h556, h695, h824, h826, h830, hc02, hlam, hphi, u0ehi0]
                                  · rcases h5bigk with h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [hlam, p832_0]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h556, hlam, p832_1]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h828, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p832_1, u2ehi3]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h556, h824, h830, hc34, hc45, hlam, hphi, p832_1]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h699, hlam, p832_1]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h824, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p832_1, u0ehi4]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [hlam, p832_0]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h824, h828, hc45, hlam, hphi, ht23, ht34, p832_1, u2ehi3]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h824, h830, hc45, hlam, hphi, ht34, p832_1, u3ehi3]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h824, hlam, p832_1]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h696, hlam, p832_1]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h822, hlam, p832_1]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [hlam, p832_0]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h830, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p832_1, u3ehi3]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h828, hlam, p832_1]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h698, hlam, p832_0]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h823, hlam, p832_0]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h827, hlam, p832_0]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [hlam, p832_0]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h830, hlam, p832_1]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p832_1, u0ehi4]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h0, h556, h695, h827, h830, hc12, hc45, hlam, hphi, ht01, ht34, p832_1, u0ehi0, u3ehi3]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht23, ht34, p832_1, u2ehi4]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [h830, hc45, hlam, hphi, ht34, p832_1, u3ehi3]
                                    · have p832_0 := h832c.1
                                      have p832_1 := h832c.2.1
                                      have p832_2 := h832c.2.2.1
                                      have p832_3 := h832c.2.2.2
                                      linarith only [hlam, p832_0]
                              · linarith only [h431, h698, h820, h826, h827, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h697, h699, h826, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h431, h698, h823, hlam]
                      · linarith only [h0, h822, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                    · linarith only [h431, h820, h821, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                  · linarith only [h0, h695, h820, hc02, hlam, hphi, u0ehi0]
              · linarith only [h697, h698, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h865 | h865
              · linarith only [h697, h865, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h867 | h867
                · rcases m.htr 1 2 3 (by decide) (by decide) with h868 | h868
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h869 | h869
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h870 | h870
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h871 | h871
                        · linarith only [h865, h871, hc13, hlam, hphi, ht01, u0ehi2]
                        · linarith only [h431, h871, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                      · linarith only [h869, h870, hc25, hlam, hphi, u2ehi3]
                    · linarith only [h0, h695, h869, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h695, h868, hc02, hlam, hphi, u0ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h877 | h877
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h878 | h878
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h879 | h879
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h880 | h880
                        · linarith only [h431, h865, h880, hc13, hlam, hphi, ht01, u0ehi0]
                        · linarith only [h431, h880, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                      · linarith only [h0, h696, h879, hlam]
                    · linarith only [h0, h696, h878, hc24, hlam, hphi, u2ehi4]
                  · linarith only [h0, h695, h877, hc02, hlam, hphi, u0ehi0]
          · linarith only [h695, h696, hc25, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h887 | h887
          · linarith only [h695, h887, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h889 | h889
            · rcases m.htr 0 3 5 (by decide) (by decide) with h890 | h890
              · rcases m.htr 0 4 5 (by decide) (by decide) with h891 | h891
                · rcases m.htr 1 2 3 (by decide) (by decide) with h892 | h892
                  · linarith only [h695, h892, hc12, hlam, hphi, ht01, u0ehi1]
                  · linarith only [h0, h892, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h895 | h895
                  · linarith only [h0, h695, h895, hc12, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h0, h895, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h889, h890, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h899 | h899
              · linarith only [h889, h899, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h901 | h901
                · rcases m.htr 1 2 3 (by decide) (by decide) with h902 | h902
                  · linarith only [h0, h695, h902, hc12, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h0, h902, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h905 | h905
                  · linarith only [h0, h695, h905, hc12, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h0, h905, hc23, hlam, hphi, ht01, ht12, u0ehi0]

end R2N4
