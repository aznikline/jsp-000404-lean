import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3302000 in
theorem n7l_sBT2_H_I_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0bigk := hb0.1
  have h5elo := hb5.1
  have h2bigk := hb2.1
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
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                                    · linarith only [h0, h10, h14, h17, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                    · linarith only [h17, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h13, h16, h3, hc24, hlam, hphi, ht45, u5elo0]
                                · linarith only [h15, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                                    · rcases h0bigk with h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [hlam, p25_0]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [h22, h24, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p25_1]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [h22, h24, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p25_1]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [h14, h22, h24, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p25_1]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        rcases p25_3 (m.d 0 1) (by simp) with h30 | h30
                                        · rcases p25_3 (m.d 0 2) (by simp) with h31 | h31
                                          · linarith only [h0, h31, hlam]
                                          · linarith only [h31, h6, hlam]
                                        · linarith only [h3, h30, hlam]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [h0, hlam, p25_1]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [hlam, p25_0]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [h14, h22, h24, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p25_1]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [h0, h14, h22, h24, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p25_1]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        rcases p25_3 (m.d 0 1) (by simp) with h39 | h39
                                        · rcases p25_3 (m.d 0 2) (by simp) with h40 | h40
                                          · rcases p25_3 (m.d 0 3) (by simp) with h41 | h41
                                            · linarith only [h4, h41, hlam]
                                            · linarith only [h41, h8, hlam]
                                          · linarith only [h40, h6, hlam]
                                        · linarith only [h3, h39, hlam]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [h1, hlam, p25_1]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [h4, hlam, p25_0]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [hlam, p25_0]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [h14, h22, h24, h7, hc03, hc45, hlam, hphi, ht0b, ht5b, p25_1]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        rcases p25_3 (m.d 0 1) (by simp) with h50 | h50
                                        · rcases p25_3 (m.d 0 2) (by simp) with h51 | h51
                                          · rcases p25_3 (m.d 0 3) (by simp) with h52 | h52
                                            · rcases p25_3 (m.d 0 4) (by simp) with h53 | h53
                                              · linarith only [h53, h7, hlam]
                                              · linarith only [h53, h9, hlam]
                                            · linarith only [h52, h8, hlam]
                                          · linarith only [h51, h6, hlam]
                                        · linarith only [h3, h50, hlam]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [h2, hlam, p25_1]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [h5, hlam, p25_0]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [h7, hlam, p25_1]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [hlam, p25_0]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        rcases p25_3 (m.d 0 1) (by simp) with h63 | h63
                                        · rcases p25_3 (m.d 0 2) (by simp) with h64 | h64
                                          · rcases p25_3 (m.d 0 3) (by simp) with h65 | h65
                                            · rcases p25_3 (m.d 0 4) (by simp) with h66 | h66
                                              · rcases p25_3 (m.d 0 5) (by simp) with h67 | h67
                                                · linarith only [h67, h9, hlam]
                                                · rcases h2bigk with h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [hlam, p69_0]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [h0, h10, h22, h24, hc01, hc45, hlam, hphi, ht0b, ht5b, p69_1]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    rcases p69_3 (m.d 0 2) (by simp) with h72 | h72
                                                    · rcases p69_3 (m.d 1 2) (by simp) with h73 | h73
                                                      · linarith only [h0, h73, hlam]
                                                      · linarith only [h10, h73, hlam]
                                                    · linarith only [h72, hlam, p69_0]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    rcases p69_3 (m.d 0 2) (by simp) with h77 | h77
                                                    · rcases p69_3 (m.d 1 2) (by simp) with h78 | h78
                                                      · linarith only [h0, h78, hlam]
                                                      · linarith only [h11, h78, hlam]
                                                    · linarith only [h77, hlam, p69_0]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [h12, h3, h4, h7, hlam, p25_1, p69_2]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [h0, hlam, p69_0]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [hlam, p69_0]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [h0, h22, h24, hc01, hc45, hlam, hphi, ht0b, ht5b, p69_1]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [h0, h14, h22, h24, hc01, hc45, hlam, hphi, ht0b, ht5b, p69_1]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    rcases p69_3 (m.d 0 2) (by simp) with h87 | h87
                                                    · rcases p69_3 (m.d 1 2) (by simp) with h88 | h88
                                                      · rcases p69_3 (m.d 2 3) (by simp) with h89 | h89
                                                        · linarith only [h10, h89, hlam]
                                                        · linarith only [h22, h89, hlam]
                                                      · linarith only [h88, hlam, p69_0]
                                                    · linarith only [h6, h87, hlam]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [h4, hlam, p69_0]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [h10, hlam, p69_0]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [hlam, p69_0]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [h14, hlam, p69_1]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [h0, h14, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p69_1]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [h5, hlam, p69_0]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [h11, hlam, p69_0]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p69_1]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [hlam, p69_0]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [h0, h11, h22, h24, hc01, hc45, hlam, hphi, ht0b, ht5b, p69_1]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [h6, hlam, p69_0]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [h12, hlam, p69_0]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [h22, hlam, p69_1]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [h23, hlam, p69_1]
                                                  · have p69_0 := h69c.1
                                                    have p69_1 := h69c.2.1
                                                    have p69_2 := h69c.2.2.1
                                                    have p69_3 := h69c.2.2.2
                                                    linarith only [hlam, p69_0]
                                              · linarith only [h66, h9, hlam]
                                            · linarith only [h65, h8, hlam]
                                          · linarith only [h6, h64, hlam]
                                        · linarith only [h3, h63, hlam]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [h3, hlam, p25_1]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [h6, hlam, p25_0]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [h8, hlam, p25_0]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [h9, hlam, p25_0]
                                      · have p25_0 := h25c.1
                                        have p25_1 := h25c.2.1
                                        have p25_2 := h25c.2.2.1
                                        have p25_3 := h25c.2.2.2
                                        linarith only [hlam, p25_0]
                                    · linarith only [h14, h24, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                  · linarith only [h13, h23, h3, hc24, hlam, hphi, ht45, u5elo0]
                                · linarith only [h22, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h13, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h12, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h123 | h123
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h124 | h124
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                              · linarith only [h0, h10, h11, h125, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h127 | h127
                                · linarith only [h0, h10, h11, h125, h127, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h127, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h11, h124, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h10, h123, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h132 | h132
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h133 | h133
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h134 | h134
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h135 | h135
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h136 | h136
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h137 | h137
                                  · linarith only [h0, h10, h132, h137, h4, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h137, hc24, hlam, hphi, ht45, u5elo4]
                                · linarith only [h10, h136, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                              · linarith only [h0, h10, h132, h135, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h134, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h132, h133, hc24, hlam, hphi, ht45, u5elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h144 | h144
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h145 | h145
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h146 | h146
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h147 | h147
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h148 | h148
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h149 | h149
                                    · rcases h0bigk with h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h144, h147, h149, hc01, hc45, hlam, hphi, ht0b, ht5b, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h1, h10, h144, h147, h149, hc01, hc45, hlam, hphi, ht0b, ht5b, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h132, h144, h147, h149, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        rcases p150_3 (m.d 0 1) (by simp) with h155 | h155
                                        · rcases p150_3 (m.d 0 2) (by simp) with h156 | h156
                                          · linarith only [h0, h156, hlam]
                                          · linarith only [h156, h6, hlam]
                                        · linarith only [h155, h3, hlam]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, hlam, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h132, h144, h146, h147, h149, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h132, h144, h147, h149, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        rcases p150_3 (m.d 0 1) (by simp) with h164 | h164
                                        · rcases p150_3 (m.d 0 2) (by simp) with h165 | h165
                                          · rcases p150_3 (m.d 0 3) (by simp) with h166 | h166
                                            · linarith only [h166, h4, hlam]
                                            · linarith only [h166, h8, hlam]
                                          · linarith only [h165, h6, hlam]
                                        · linarith only [h164, h3, hlam]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h1, hlam, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h4, hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h132, h144, h147, h149, h5, hc03, hc45, hlam, hphi, ht0b, ht5b, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        rcases p150_3 (m.d 0 1) (by simp) with h175 | h175
                                        · rcases p150_3 (m.d 0 2) (by simp) with h176 | h176
                                          · rcases p150_3 (m.d 0 3) (by simp) with h177 | h177
                                            · rcases p150_3 (m.d 0 4) (by simp) with h178 | h178
                                              · linarith only [h178, h7, hlam]
                                              · linarith only [h178, h9, hlam]
                                            · linarith only [h177, h8, hlam]
                                          · linarith only [h176, h6, hlam]
                                        · linarith only [h175, h3, hlam]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h2, hlam, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h5, hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h7, hlam, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        rcases p150_3 (m.d 0 1) (by simp) with h188 | h188
                                        · rcases p150_3 (m.d 0 2) (by simp) with h189 | h189
                                          · rcases p150_3 (m.d 0 3) (by simp) with h190 | h190
                                            · rcases p150_3 (m.d 0 4) (by simp) with h191 | h191
                                              · rcases p150_3 (m.d 0 5) (by simp) with h192 | h192
                                                · linarith only [h192, h9, hlam]
                                                · rcases h2bigk with h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [hlam, p194_0]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    rcases p194_3 (m.d 0 2) (by simp) with h196 | h196
                                                    · rcases p194_3 (m.d 1 2) (by simp) with h197 | h197
                                                      · linarith only [h0, h197, hlam]
                                                      · rcases p194_3 (m.d 2 3) (by simp) with h199 | h199
                                                        · linarith only [h199, h4, hlam]
                                                        · linarith only [h10, h199, hlam]
                                                    · linarith only [h0, h196, hlam]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [h0, h132, h144, h146, h147, h149, hc01, hc45, hlam, hphi, ht0b, ht5b, p194_1]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [h0, h132, h144, h147, h149, hc01, hc45, hlam, hphi, ht0b, ht5b, p194_1]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [h132, h144, h146, h4, hlam, p194_2]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [h0, hlam, p194_0]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [hlam, p194_0]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [h10, hlam, p194_0]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [h132, hlam, p194_0]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [h132, h146, h4, hc02, hc25, hlam, hphi, ht0b, ht5b, p194_1]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [h4, hlam, p194_0]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [h0, h144, h147, h149, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p194_1]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [hlam, p194_0]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [h0, h132, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p194_1]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    rcases p194_3 (m.d 0 2) (by simp) with h215 | h215
                                                    · rcases p194_3 (m.d 1 2) (by simp) with h216 | h216
                                                      · linarith only [h10, h216, hlam]
                                                      · linarith only [h144, h216, hlam]
                                                    · linarith only [h215, h6, hlam]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [h5, hlam, p194_0]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [h0, h144, h147, h149, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p194_1]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [h146, hlam, p194_0]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [hlam, p194_0]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    rcases p194_3 (m.d 0 2) (by simp) with h224 | h224
                                                    · rcases p194_3 (m.d 1 2) (by simp) with h225 | h225
                                                      · linarith only [h132, h225, hlam]
                                                      · linarith only [h144, h225, hlam]
                                                    · linarith only [h224, h6, hlam]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [h6, hlam, p194_0]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [h144, hlam, p194_0]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [h147, hlam, p194_1]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [h148, hlam, p194_1]
                                                  · have p194_0 := h194c.1
                                                    have p194_1 := h194c.2.1
                                                    have p194_2 := h194c.2.2.1
                                                    have p194_3 := h194c.2.2.2
                                                    linarith only [hlam, p194_0]
                                              · linarith only [h191, h9, hlam]
                                            · linarith only [h190, h8, hlam]
                                          · linarith only [h189, h6, hlam]
                                        · linarith only [h188, h3, hlam]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h3, hlam, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h6, hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h8, hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h9, hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [hlam, p150_0]
                                    · linarith only [h149, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h132, h145, h148, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                                · linarith only [h147, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h0, h10, h144, h146, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h132, h144, h145, hc25, hlam, hphi, u5elo4]
                          · linarith only [h144, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h9, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h8, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h251 | h251
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h252 | h252
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h253 | h253
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h254 | h254
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h255 | h255
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h256 | h256
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h257 | h257
                              · linarith only [h1, h253, h257, h7, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h259 | h259
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h260 | h260
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h261 | h261
                                    · rcases h0bigk with h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [hlam, p262_0]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [h0, h254, h257, h259, h261, hc01, hc45, hlam, hphi, ht0b, ht5b, p262_1]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [h1, h253, h259, h261, hc01, hc45, hlam, hphi, ht0b, ht5b, p262_1]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [h1, h253, h259, h261, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p262_1]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        rcases p262_3 (m.d 0 1) (by simp) with h267 | h267
                                        · rcases p262_3 (m.d 0 2) (by simp) with h268 | h268
                                          · linarith only [h0, h268, hlam]
                                          · linarith only [h268, h6, hlam]
                                        · linarith only [h267, h3, hlam]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [h0, hlam, p262_1]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [hlam, p262_0]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [h1, h253, h259, h261, hc02, hc45, hlam, hphi, ht0b, ht5b, p262_1]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [h0, h1, h253, h259, h261, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p262_1]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        rcases p262_3 (m.d 0 1) (by simp) with h276 | h276
                                        · rcases p262_3 (m.d 0 2) (by simp) with h277 | h277
                                          · rcases p262_3 (m.d 0 3) (by simp) with h278 | h278
                                            · linarith only [h278, h4, hlam]
                                            · linarith only [h251, h278, hlam]
                                          · linarith only [h277, h6, hlam]
                                        · linarith only [h276, h3, hlam]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [h1, hlam, p262_1]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [h4, hlam, p262_0]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [hlam, p262_0]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [h7, hlam, p262_0]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [h7, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p262_1]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [h2, hlam, p262_1]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [h5, hlam, p262_0]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [h1, h253, h259, h261, hc04, hc45, hlam, hphi, ht0b, ht5b, p262_1]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [hlam, p262_0]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        rcases p262_3 (m.d 0 1) (by simp) with h292 | h292
                                        · rcases p262_3 (m.d 0 2) (by simp) with h293 | h293
                                          · rcases p262_3 (m.d 0 3) (by simp) with h294 | h294
                                            · linarith only [h294, h7, hlam]
                                            · linarith only [h251, h294, hlam]
                                          · linarith only [h293, h6, hlam]
                                        · linarith only [h292, h3, hlam]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [h3, hlam, p262_1]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [h6, hlam, p262_0]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [h251, hlam, p262_0]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [h252, hlam, p262_0]
                                      · have p262_0 := h262c.1
                                        have p262_1 := h262c.2.1
                                        have p262_2 := h262c.2.2.1
                                        have p262_3 := h262c.2.2.2
                                        linarith only [hlam, p262_0]
                                    · linarith only [h261, h7, hc04, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h256, h257, h260, h3, hc23, hlam, hphi, ht34, ht45, u5elo0]
                                · linarith only [h251, h259, h7, hc23, hc34, hlam, hphi]
                            · linarith only [h256, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h255, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h309 | h309
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h310 | h310
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h311 | h311
                              · linarith only [h253, h254, h311, h5, h7, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h313 | h313
                                · linarith only [h0, h253, h254, h313, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h313, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h254, h310, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h253, h309, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h318 | h318
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h319 | h319
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h320 | h320
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h321 | h321
                              · linarith only [h321, h4, h7, hlam]
                              · linarith only [h253, h318, h321, hlam]
                            · linarith only [h320, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h318, h319, hc24, hlam, hphi, ht45, u5elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h326 | h326
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h327 | h327
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h328 | h328
                              · linarith only [h328, h4, h7, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h330 | h330
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h331 | h331
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h332 | h332
                                    · rcases h0bigk with h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [hlam, p333_0]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [h0, h326, h330, h332, hc01, hc45, hlam, hphi, ht0b, ht5b, p333_1]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [h253, h326, h330, h332, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p333_1]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [h2, h318, h326, h330, h332, hc01, hc45, hlam, hphi, ht0b, ht5b, p333_1]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        rcases p333_3 (m.d 0 1) (by simp) with h338 | h338
                                        · rcases p333_3 (m.d 0 2) (by simp) with h339 | h339
                                          · linarith only [h0, h339, hlam]
                                          · linarith only [h339, h6, hlam]
                                        · linarith only [h3, h338, hlam]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [h0, hlam, p333_1]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [hlam, p333_0]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [h253, h326, h330, h332, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p333_1]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [h0, h253, h326, h328, h330, h332, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p333_1]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        rcases p333_3 (m.d 0 1) (by simp) with h347 | h347
                                        · rcases p333_3 (m.d 0 2) (by simp) with h348 | h348
                                          · rcases p333_3 (m.d 0 3) (by simp) with h349 | h349
                                            · linarith only [h349, h4, hlam]
                                            · linarith only [h251, h349, hlam]
                                          · linarith only [h348, h6, hlam]
                                        · linarith only [h3, h347, hlam]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [h1, hlam, p333_1]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [h4, hlam, p333_0]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [hlam, p333_0]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [h7, hlam, p333_0]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [h7, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p333_1]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [h2, hlam, p333_1]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [h5, hlam, p333_0]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [h253, h4, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p333_1]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [hlam, p333_0]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        rcases p333_3 (m.d 0 1) (by simp) with h363 | h363
                                        · rcases p333_3 (m.d 0 2) (by simp) with h364 | h364
                                          · rcases p333_3 (m.d 0 3) (by simp) with h365 | h365
                                            · linarith only [h365, h7, hlam]
                                            · linarith only [h251, h365, hlam]
                                          · linarith only [h364, h6, hlam]
                                        · linarith only [h3, h363, hlam]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [h3, hlam, p333_1]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [h6, hlam, p333_0]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [h251, hlam, p333_0]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [h252, hlam, p333_0]
                                      · have p333_0 := h333c.1
                                        have p333_1 := h333c.2.1
                                        have p333_2 := h333c.2.2.1
                                        have p333_3 := h333c.2.2.2
                                        linarith only [hlam, p333_0]
                                    · linarith only [h332, h7, hc04, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h253, h326, h327, h328, h331, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h253, h326, h330, hc25, hlam, hphi, u5elo3]
                            · linarith only [h327, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h326, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h252, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h251, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h6, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h383 | h383
              · rcases m.htr 0 3 4 (by decide) (by decide) with h384 | h384
                · linarith only [h384, h4, h5, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h386 | h386
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h387 | h387
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h388 | h388
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h389 | h389
                        · linarith only [h0, h389, h5, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h391 | h391
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h392 | h392
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h393 | h393
                              · linarith only [h0, h384, h388, h393, h5, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h395 | h395
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h396 | h396
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h397 | h397
                                    · rcases h0bigk with h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [hlam, p398_0]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h395, h397, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h1, h388, h395, h397, hc01, hc45, hlam, hphi, ht0b, ht5b, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h395, h397, h4, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        rcases p398_3 (m.d 0 1) (by simp) with h403 | h403
                                        · rcases p398_3 (m.d 0 2) (by simp) with h404 | h404
                                          · linarith only [h0, h404, hlam]
                                          · linarith only [h383, h404, hlam]
                                        · linarith only [h3, h403, hlam]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h0, hlam, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [hlam, p398_0]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h1, h388, h395, h397, hc02, hc45, hlam, hphi, ht0b, ht5b, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h5, hlam, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h393, h5, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h1, hlam, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h4, hlam, p398_0]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [hlam, p398_0]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h384, hlam, p398_0]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h3, h391, h393, h4, h5, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h2, hlam, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h393, h5, hc02, hc34, hlam, hphi, ht23, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h393, h5, hc03, hc34, hlam, hphi, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [hlam, p398_0]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        rcases p398_3 (m.d 0 1) (by simp) with h422 | h422
                                        · rcases p398_3 (m.d 0 2) (by simp) with h423 | h423
                                          · linarith only [h423, h5, hlam]
                                          · linarith only [h383, h423, hlam]
                                        · linarith only [h3, h422, hlam]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h3, hlam, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h383, hlam, p398_0]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h386, hlam, p398_0]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h387, hlam, p398_0]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [hlam, p398_0]
                                    · linarith only [h393, h397, h5, hc04, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h3, h392, h396, h5, hc02, hlam, hphi, ht23, ht34, ht45, u5elo0]
                                · linarith only [h395, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h388, h389, h392, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h388, h391, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h388, h4, h5, hc12, hc24, hlam, hphi]
                    · linarith only [h387, h5, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1, h386, hc13, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h383, h4, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h441 | h441
            · rcases m.htr 0 2 5 (by decide) (by decide) with h442 | h442
              · rcases m.htr 0 3 4 (by decide) (by decide) with h443 | h443
                · rcases m.htr 0 3 5 (by decide) (by decide) with h444 | h444
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h445 | h445
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h446 | h446
                      · linarith only [h0, h4, h441, h446, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h448 | h448
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h449 | h449
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h450 | h450
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h451 | h451
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h452 | h452
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h453 | h453
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h454 | h454
                                    · rcases h0bigk with h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [hlam, p455_0]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h0, h448, h451, h454, hc01, hc45, hlam, hphi, ht0b, ht5b, p455_1]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h0, h4, h448, h451, h454, hc01, hc45, hlam, hphi, ht0b, ht5b, p455_1]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h441, h451, h454, hc01, hc45, hlam, hphi, ht0b, ht5b, p455_1]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        rcases p455_3 (m.d 0 1) (by simp) with h460 | h460
                                        · rcases p455_3 (m.d 0 2) (by simp) with h461 | h461
                                          · linarith only [h0, h461, hlam]
                                          · linarith only [h442, h461, hlam]
                                        · linarith only [h3, h460, hlam]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h0, hlam, p455_1]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [hlam, p455_0]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h4, hlam, p455_1]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h2, h448, h451, h454, hc02, hc45, hlam, hphi, ht0b, ht5b, p455_1]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p455_1]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h1, hlam, p455_1]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h4, hc02, hc23, hlam, hphi, p455_1]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [hlam, p455_0]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h2, h4, h448, h451, h454, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p455_1]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        rcases p455_3 (m.d 0 1) (by simp) with h474 | h474
                                        · rcases p455_3 (m.d 0 2) (by simp) with h475 | h475
                                          · linarith only [h4, h475, hlam]
                                          · linarith only [h442, h475, hlam]
                                        · linarith only [h3, h474, hlam]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h2, hlam, p455_1]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h441, hlam, p455_0]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h443, hlam, p455_1]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [hlam, p455_0]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h3, h4, h441, h449, h452, h454, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p455_1]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h3, hlam, p455_1]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h442, hlam, p455_0]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h444, hlam, p455_0]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [h445, hlam, p455_0]
                                      · have p455_0 := h455c.1
                                        have p455_1 := h455c.2.1
                                        have p455_2 := h455c.2.2.1
                                        have p455_3 := h455c.2.2.2
                                        linarith only [hlam, p455_0]
                                    · linarith only [h454, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h3, h450, h453, hc24, hlam, hphi, ht45, u5elo0]
                                · linarith only [h4, h452, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                              · linarith only [h4, h443, h451, hlam]
                            · linarith only [h450, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h448, h449, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h4, h441, h448, hc12, hc23, hlam, hphi]
                    · linarith only [h445, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h444, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h4, h441, h443, hlam]
              · linarith only [h442, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h500 | h500
              · rcases m.htr 0 3 4 (by decide) (by decide) with h501 | h501
                · rcases m.htr 0 3 5 (by decide) (by decide) with h502 | h502
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h503 | h503
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h504 | h504
                      · linarith only [h0, h4, h504, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h506 | h506
                        · linarith only [h0, h441, h506, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h508 | h508
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h509 | h509
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h510 | h510
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h511 | h511
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h512 | h512
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h513 | h513
                                    · rcases h0bigk with h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [hlam, p514_0]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [h500, h511, h513, hc01, hc45, hlam, hphi, ht0b, ht5b, p514_1]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [h501, h513, hc01, hc45, hlam, hphi, ht0b, ht5b, p514_1]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [h441, h500, h511, h513, hc01, hc45, hlam, hphi, ht0b, ht5b, p514_1]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        rcases p514_3 (m.d 0 1) (by simp) with h519 | h519
                                        · rcases p514_3 (m.d 0 2) (by simp) with h520 | h520
                                          · linarith only [h0, h520, hlam]
                                          · linarith only [h500, h520, hlam]
                                        · linarith only [h3, h519, hlam]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [h0, hlam, p514_1]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [hlam, p514_0]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [h4, hlam, p514_1]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [h441, hlam, p514_1]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [h3, h441, h510, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p514_1]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [h1, hlam, p514_1]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [h0, h508, hc03, hc25, hlam, hphi, ht0b, ht5b, p514_1]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [hlam, p514_0]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [h0, h4, h441, h508, h511, h513, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p514_1]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        rcases p514_3 (m.d 0 1) (by simp) with h533 | h533
                                        · rcases p514_3 (m.d 0 2) (by simp) with h534 | h534
                                          · linarith only [h4, h534, hlam]
                                          · linarith only [h500, h534, hlam]
                                        · linarith only [h3, h533, hlam]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [h2, hlam, p514_1]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [h0, h508, h511, h513, hc04, hc45, hlam, hphi, ht0b, ht5b, p514_1]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [h501, hlam, p514_1]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [hlam, p514_0]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        rcases p514_3 (m.d 0 1) (by simp) with h542 | h542
                                        · rcases p514_3 (m.d 0 2) (by simp) with h543 | h543
                                          · linarith only [h441, h543, hlam]
                                          · linarith only [h500, h543, hlam]
                                        · linarith only [h3, h542, hlam]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [h3, hlam, p514_1]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [h500, hlam, p514_0]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [h502, hlam, p514_0]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [h503, hlam, p514_0]
                                      · have p514_0 := h514c.1
                                        have p514_1 := h514c.2.1
                                        have p514_2 := h514c.2.2.1
                                        have p514_3 := h514c.2.2.2
                                        linarith only [hlam, p514_0]
                                    · linarith only [h513, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h3, h509, h512, hc24, hlam, hphi, ht45, u5elo0]
                                · linarith only [h4, h511, hc03, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h0, h4, h501, h508, h510, hc03, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h506, h508, h509, hc25, hlam, hphi, u5elo4]
                          · linarith only [h508, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h503, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h502, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h560 | h560
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h561 | h561
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h562 | h562
                      · linarith only [h0, h4, h562, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h564 | h564
                        · linarith only [h0, h441, h564, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h566 | h566
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h567 | h567
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h568 | h568
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h569 | h569
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h570 | h570
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h571 | h571
                                    · rcases h0bigk with h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [hlam, p572_0]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h0, h566, h569, h571, hc01, hc45, hlam, hphi, ht0b, ht5b, p572_1]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h0, h4, h566, h569, h571, hc01, hc45, hlam, hphi, ht0b, ht5b, p572_1]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h2, h564, h566, h569, h571, hc01, hc45, hlam, hphi, ht0b, ht5b, p572_1]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        rcases p572_3 (m.d 0 1) (by simp) with h577 | h577
                                        · rcases p572_3 (m.d 0 2) (by simp) with h578 | h578
                                          · linarith only [h0, h578, hlam]
                                          · linarith only [h500, h578, hlam]
                                        · linarith only [h3, h577, hlam]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h0, hlam, p572_1]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [hlam, p572_0]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h4, hlam, p572_1]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h441, hlam, p572_1]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h3, h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p572_1]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h1, hlam, p572_1]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h0, h501, h566, h569, h571, hc04, hc45, hlam, hphi, ht0b, ht5b, p572_1]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [hlam, p572_0]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h501, hlam, p572_0]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h500, h501, h568, h569, h571, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p572_1]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h2, hlam, p572_1]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h0, h501, h566, h568, h569, h571, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p572_1]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h501, h568, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p572_1]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [hlam, p572_0]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h500, h501, h568, h569, h571, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p572_1]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h3, hlam, p572_1]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h500, hlam, p572_0]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h560, hlam, p572_0]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [h561, hlam, p572_0]
                                      · have p572_0 := h572c.1
                                        have p572_1 := h572c.2.1
                                        have p572_2 := h572c.2.2.1
                                        have p572_3 := h572c.2.2.2
                                        linarith only [hlam, p572_0]
                                    · linarith only [h501, h571, hc04, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h3, h4, h501, h567, h568, h570, hc02, hlam, hphi, ht23, ht34, ht45, u5elo0]
                                · linarith only [h0, h4, h501, h566, h568, h569, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h605 | h605
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h606 | h606
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h607 | h607
                                    · rcases h0bigk with h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [hlam, p608_0]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h0, h566, h605, h607, hc01, hc45, hlam, hphi, ht0b, ht5b, p608_1]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h0, h4, h566, h605, h607, hc01, hc45, hlam, hphi, ht0b, ht5b, p608_1]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h0, h4, h501, h566, h605, h607, hc01, hc45, hlam, hphi, ht0b, ht5b, p608_1]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        rcases p608_3 (m.d 0 1) (by simp) with h613 | h613
                                        · rcases p608_3 (m.d 0 2) (by simp) with h614 | h614
                                          · linarith only [h0, h614, hlam]
                                          · linarith only [h500, h614, hlam]
                                        · linarith only [h3, h613, hlam]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h0, hlam, p608_1]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [hlam, p608_0]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h4, hlam, p608_1]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h441, hlam, p608_1]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h3, h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p608_1]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h1, hlam, p608_1]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h0, h4, hc12, hc23, hlam, hphi, p608_1]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [hlam, p608_0]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h501, hlam, p608_0]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h501, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p608_1]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h2, hlam, p608_1]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h0, h501, hc12, hc34, hlam, hphi, ht23, p608_1]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h501, hc03, hc34, hlam, hphi, p608_1]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [hlam, p608_0]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        rcases p608_3 (m.d 0 1) (by simp) with h632 | h632
                                        · rcases p608_3 (m.d 0 2) (by simp) with h633 | h633
                                          · linarith only [h441, h633, hlam]
                                          · linarith only [h500, h633, hlam]
                                        · linarith only [h3, h632, hlam]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h3, hlam, p608_1]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h500, hlam, p608_0]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h560, hlam, p608_0]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [h561, hlam, p608_0]
                                      · have p608_0 := h608c.1
                                        have p608_1 := h608c.2.1
                                        have p608_2 := h608c.2.2.1
                                        have p608_3 := h608c.2.2.2
                                        linarith only [hlam, p608_0]
                                    · linarith only [h568, h607, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                  · linarith only [h3, h4, h567, h568, h606, hc02, hlam, hphi, ht23, ht34, ht45, u5elo0]
                                · linarith only [h0, h4, h566, h605, hc25, hlam, hphi, u5elo3]
                            · linarith only [h564, h566, h567, hc25, hlam, hphi, u5elo4]
                          · linarith only [h566, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h4, h501, h561, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h4, h500, h560, hc25, hlam, hphi, u5elo3]
              · linarith only [h500, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h651 | h651
        · rcases m.htr 0 2 3 (by decide) (by decide) with h652 | h652
          · rcases m.htr 0 2 4 (by decide) (by decide) with h653 | h653
            · linarith only [h0, h2, h653, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h655 | h655
              · rcases m.htr 0 3 4 (by decide) (by decide) with h656 | h656
                · linarith only [h1, h2, h656, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h658 | h658
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h659 | h659
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h660 | h660
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h661 | h661
                        · linarith only [h0, h2, h653, h661, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h663 | h663
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h664 | h664
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h665 | h665
                              · linarith only [h0, h2, h656, h660, h665, hlam]
                              · linarith only [h0, h2, h660, h661, h665, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h2, h660, h664, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h660, h663, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h652, h653, h660, hc12, hc24, hlam, hphi]
                    · linarith only [h2, h659, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h658, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h655, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h674 | h674
            · linarith only [h0, h2, h674, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h676 | h676
              · rcases m.htr 0 3 4 (by decide) (by decide) with h677 | h677
                · linarith only [h1, h2, h677, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h679 | h679
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h680 | h680
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h681 | h681
                      · linarith only [h0, h652, h676, h681, hc01, hc25, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h683 | h683
                        · linarith only [h0, h674, h683, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h685 | h685
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h686 | h686
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h687 | h687
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h688 | h688
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h689 | h689
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h690 | h690
                                    · rcases h0bigk with h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h0, h2, h677, h685, h687, h688, h690, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h2, h677, h687, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h2, hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h2, h677, h687, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h0, hlam, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h652, hlam, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h674, hlam, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h0, h2, h651, h677, h687, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h1, hlam, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h0, h685, h688, h690, hc03, hc45, hlam, hphi, ht0b, ht5b, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h677, hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h676, h677, h687, h688, h690, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h677, h687, hc01, hc23, hlam, hphi, ht12, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h0, h677, h685, h687, h688, h690, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h677, h687, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h676, h677, h687, h688, h690, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h651, hlam, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h676, hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h679, hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h680, hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [hlam, p691_0]
                                    · linarith only [h677, h690, hc04, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h1, h2, h681, h683, h689, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h1, h2, h681, h683, h685, h687, h688, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h720 | h720
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h721 | h721
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h722 | h722
                                    · rcases h0bigk with h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h0, h685, h720, h722, hc01, hc45, hlam, hphi, ht0b, ht5b, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h1, h2, h681, h683, h685, h720, h722, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h2, hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h2, h683, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h0, hlam, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h652, hlam, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h674, hlam, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h0, h2, h651, h683, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h1, hlam, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h0, h685, h720, h722, hc03, hc45, hlam, hphi, ht0b, ht5b, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h677, hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h1, h2, h676, h683, h720, h722, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h2, h683, hc01, hc24, hlam, hphi, ht12, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h0, h2, h683, h685, h720, h722, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h1, h2, h681, h683, h685, h720, h722, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        rcases p723_3 (m.d 0 1) (by simp) with h743 | h743
                                        · linarith only [h2, h743, hlam]
                                        · linarith only [h651, h743, hlam]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h651, hlam, p723_1]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h676, hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h679, hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [h680, hlam, p723_0]
                                      · have p723_0 := h723c.1
                                        have p723_1 := h723c.2.1
                                        have p723_2 := h723c.2.2.1
                                        have p723_3 := h723c.2.2.2
                                        linarith only [hlam, p723_0]
                                    · linarith only [h687, h722, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                  · linarith only [h1, h2, h681, h683, h721, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h0, h652, h685, h720, hc25, hlam, hphi, u5elo3]
                            · linarith only [h1, h2, h681, h685, h686, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h685, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h2, h680, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h652, h676, h679, hc25, hlam, hphi, u5elo3]
              · linarith only [h676, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h651, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h760 | h760
      · rcases m.htr 0 1 5 (by decide) (by decide) with h761 | h761
        · rcases m.htr 0 2 3 (by decide) (by decide) with h762 | h762
          · linarith only [h0, h1, h762, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h764 | h764
            · rcases m.htr 0 2 5 (by decide) (by decide) with h765 | h765
              · rcases m.htr 0 3 4 (by decide) (by decide) with h766 | h766
                · rcases m.htr 0 3 5 (by decide) (by decide) with h767 | h767
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h768 | h768
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h769 | h769
                      · linarith only [h0, h1, h762, h769, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h771 | h771
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h772 | h772
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h773 | h773
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h774 | h774
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h775 | h775
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h776 | h776
                                  · linarith only [h0, h1, h769, h771, h776, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · linarith only [h776, hc24, hlam, hphi, ht45, u5elo4]
                                · linarith only [h0, h1, h769, h775, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h769, h771, h773, h774, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h773, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h771, h772, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h0, h1, h764, h769, h771, hc12, hc23, hlam, hphi]
                    · linarith only [h768, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1, h767, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h1, h760, h766, hlam]
              · linarith only [h764, h765, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h788 | h788
              · rcases m.htr 0 3 4 (by decide) (by decide) with h789 | h789
                · rcases m.htr 0 3 5 (by decide) (by decide) with h790 | h790
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h791 | h791
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h792 | h792
                      · linarith only [h0, h762, h792, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h794 | h794
                        · linarith only [h0, h764, h788, h794, hc01, hc25, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h796 | h796
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h797 | h797
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h798 | h798
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h799 | h799
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h800 | h800
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h801 | h801
                                    · rcases h0bigk with h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [hlam, p802_0]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h0, h1, h792, h796, h799, h801, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p802_1]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h1, hlam, p802_0]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h0, h1, h764, h792, h796, h799, h801, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p802_1]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h1, h792, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p802_1]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h0, hlam, p802_1]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [hlam, p802_0]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h762, hlam, p802_1]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h764, hlam, p802_1]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h761, h764, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p802_1]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h1, h792, hc01, hc23, hlam, hphi, ht12, p802_1]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h1, h792, hc02, hc23, hlam, hphi, p802_1]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [hlam, p802_0]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h1, h760, h792, h794, h796, h799, h801, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p802_1]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        rcases p802_3 (m.d 0 1) (by simp) with h817 | h817
                                        · linarith only [h1, h817, hlam]
                                        · linarith only [h761, h817, hlam]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h760, hlam, p802_1]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h0, h796, h799, h801, hc04, hc45, hlam, hphi, ht0b, ht5b, p802_1]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h789, hlam, p802_1]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [hlam, p802_0]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h1, h760, h761, h792, h796, h799, h801, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p802_1]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h761, hlam, p802_1]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h788, hlam, p802_0]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h790, hlam, p802_0]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [h791, hlam, p802_0]
                                      · have p802_0 := h802c.1
                                        have p802_1 := h802c.2.1
                                        have p802_2 := h802c.2.2.1
                                        have p802_3 := h802c.2.2.2
                                        linarith only [hlam, p802_0]
                                    · linarith only [h801, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h761, h797, h800, hc24, hlam, hphi, ht45, u5elo0]
                                · linarith only [h1, h792, h799, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                              · linarith only [h1, h760, h792, h794, h798, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h794, h796, h797, hc25, hlam, hphi, u5elo4]
                          · linarith only [h796, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h791, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1, h790, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h1, h760, h789, hlam]
              · linarith only [h788, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h761, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h841 | h841
        · rcases m.htr 0 2 3 (by decide) (by decide) with h842 | h842
          · linarith only [h0, h1, h842, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h844 | h844
            · linarith only [h0, h760, h844, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h846 | h846
              · rcases m.htr 0 3 4 (by decide) (by decide) with h847 | h847
                · rcases m.htr 0 3 5 (by decide) (by decide) with h848 | h848
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h849 | h849
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h850 | h850
                      · linarith only [h0, h1, h842, h850, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h852 | h852
                        · linarith only [h0, h760, h844, h852, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h854 | h854
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h855 | h855
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h856 | h856
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h857 | h857
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h858 | h858
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h859 | h859
                                    · rcases h0bigk with h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h760, h852, h856, hc02, hc23, hlam, hphi, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h1, hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h760, hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h760, h852, h856, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h0, hlam, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h842, hlam, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h844, hlam, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h0, h760, h841, h852, h856, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h1, h850, hc02, hc23, hlam, hphi, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h0, h1, h760, h850, hc12, hc23, hlam, hphi, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        rcases p860_3 (m.d 0 1) (by simp) with h875 | h875
                                        · linarith only [h1, h875, hlam]
                                        · linarith only [h841, h875, hlam]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h0, h854, h857, h859, hc04, hc45, hlam, hphi, ht0b, ht5b, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h0, h760, h852, h854, h856, h857, h859, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h847, hlam, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        rcases p860_3 (m.d 0 1) (by simp) with h882 | h882
                                        · linarith only [h760, h882, hlam]
                                        · linarith only [h841, h882, hlam]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h841, hlam, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h846, hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h848, hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h849, hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [hlam, p860_0]
                                    · linarith only [h859, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h760, h841, h852, h855, h858, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                                · linarith only [h0, h760, h852, h854, h856, h857, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h0, h1, h850, h854, h856, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h0, h760, h854, h855, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h854, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h849, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h848, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h898 | h898
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h899 | h899
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h900 | h900
                      · linarith only [h0, h842, h846, h900, hc01, hc25, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h902 | h902
                        · linarith only [h0, h844, h902, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h904 | h904
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h905 | h905
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h906 | h906
                              · linarith only [h0, h1, h847, h904, h906, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h0, h1, h900, h904, h906, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h0, h760, h904, h905, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h904, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h1, h847, h899, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h0, h1, h898, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h846, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h841, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h915 | h915
    · rcases m.htr 0 1 4 (by decide) (by decide) with h916 | h916
      · rcases m.htr 0 1 5 (by decide) (by decide) with h917 | h917
        · rcases m.htr 0 2 3 (by decide) (by decide) with h918 | h918
          · rcases m.htr 0 2 4 (by decide) (by decide) with h919 | h919
            · rcases m.htr 0 2 5 (by decide) (by decide) with h920 | h920
              · rcases m.htr 0 3 4 (by decide) (by decide) with h921 | h921
                · rcases m.htr 0 3 5 (by decide) (by decide) with h922 | h922
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h923 | h923
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h924 | h924
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h925 | h925
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h926 | h926
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h927 | h927
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h928 | h928
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h929 | h929
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h930 | h930
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h931 | h931
                                    · linarith only [h0, h915, h924, h928, h931, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h931, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h0, h916, h927, h930, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h929, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h936 | h936
                                · linarith only [h0, h915, h921, h928, h936, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h936, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h927, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h926, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h915, h919, h925, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h918, h924, hlam]
                    · linarith only [h923, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h922, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h945 | h945
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h946 | h946
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h947 | h947
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h948 | h948
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h949 | h949
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h950 | h950
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h951 | h951
                              · linarith only [h915, h921, h945, h947, h951, hc01, hc35, hlam, hphi, ht0b, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h953 | h953
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h954 | h954
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h955 | h955
                                    · rcases h0bigk with h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [hlam, p956_0]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h0, hlam, p956_0]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h0, h915, h947, h953, h955, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p956_1]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h0, h915, h921, h947, h953, h955, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p956_1]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p956_1]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p956_1]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [hlam, p956_0]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h0, h915, h947, h953, h955, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p956_1]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h0, h915, h921, h947, h953, h955, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p956_1]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        rcases p956_3 (m.d 0 1) (by simp) with h966 | h966
                                        · linarith only [h0, h966, hlam]
                                        · linarith only [h917, h966, hlam]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h915, hlam, p956_1]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h918, hlam, p956_0]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [hlam, p956_0]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h921, hlam, p956_0]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h917, h921, h949, h953, h955, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p956_1]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h916, hlam, p956_1]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h919, hlam, p956_0]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h915, h947, h953, h955, hc04, hc45, hlam, hphi, ht0b, ht5b, p956_1]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [hlam, p956_0]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h0, h916, h917, h949, h953, h955, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p956_1]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h917, hlam, p956_1]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h920, hlam, p956_0]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h945, hlam, p956_0]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [h946, hlam, p956_0]
                                      · have p956_0 := h956c.1
                                        have p956_1 := h956c.2.1
                                        have p956_2 := h956c.2.2.1
                                        have p956_3 := h956c.2.2.2
                                        linarith only [hlam, p956_0]
                                    · linarith only [h955, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h917, h950, h951, h954, hc23, hlam, hphi, ht34, ht45, u5elo0]
                                · linarith only [h953, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h950, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h949, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h919, h948, hlam]
                      · linarith only [h0, h918, h947, hlam]
                    · linarith only [h921, h946, hc03, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h918, h945, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h920, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h916, h919, hlam]
          · linarith only [h0, h915, h918, hlam]
        · linarith only [h917, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h997 | h997
        · rcases m.htr 0 2 3 (by decide) (by decide) with h998 | h998
          · rcases m.htr 0 2 4 (by decide) (by decide) with h999 | h999
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1000 | h1000
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1001 | h1001
                · linarith only [h1001, h915, h916, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1003 | h1003
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1004 | h1004
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1005 | h1005
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1006 | h1006
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1007 | h1007
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1008 | h1008
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1009 | h1009
                              · linarith only [h1001, h1005, h1006, h1009, h915, h916, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1011 | h1011
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1012 | h1012
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1013 | h1013
                                    · rcases h0bigk with h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [hlam, p1014_0]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h0, hlam, p1014_0]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h1005, h1006, h1011, h1013, h915, h916, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1014_1]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h916, hlam, p1014_0]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h1006, h916, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1014_1]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1014_1]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [hlam, p1014_0]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h0, h1005, h1011, h1013, h915, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1014_1]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h0, h1005, h1011, h1013, h915, h916, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1014_1]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        rcases p1014_3 (m.d 0 1) (by simp) with h1024 | h1024
                                        · linarith only [h0, h1024, hlam]
                                        · linarith only [h1024, h997, hlam]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h915, hlam, p1014_1]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h998, hlam, p1014_0]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [hlam, p1014_0]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h1001, hlam, p1014_0]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h0, h1007, h1011, h1013, h915, h997, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1014_1]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h1001, hc01, hc34, hlam, hphi, ht12, ht23, p1014_1]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h999, hlam, p1014_0]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h1001, hc03, hc34, hlam, hphi, p1014_1]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [hlam, p1014_0]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        rcases p1014_3 (m.d 0 1) (by simp) with h1036 | h1036
                                        · linarith only [h1036, h916, hlam]
                                        · linarith only [h1036, h997, hlam]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h997, hlam, p1014_1]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h1000, hlam, p1014_0]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h1003, hlam, p1014_0]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [h1004, hlam, p1014_0]
                                      · have p1014_0 := h1014c.1
                                        have p1014_1 := h1014c.2.1
                                        have p1014_2 := h1014c.2.2.1
                                        have p1014_3 := h1014c.2.2.2
                                        linarith only [hlam, p1014_0]
                                    · linarith only [h1001, h1013, hc04, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h1008, h1012, h997, hc24, hlam, hphi, ht45, u5elo0]
                                · linarith only [h1011, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h1008, h915, h916, hc13, hc45, hlam, hphi, ht34]
                          · linarith only [h1000, h1006, h1007, h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                        · linarith only [h0, h1006, h999, hlam]
                      · linarith only [h0, h1005, h915, h998, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1004, h915, h916, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h1003, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h1000, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1054 | h1054
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1055 | h1055
                · linarith only [h0, h1055, h915, h999, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1057 | h1057
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1058 | h1058
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1059 | h1059
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1060 | h1060
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1061 | h1061
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1062 | h1062
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1063 | h1063
                              · linarith only [h0, h1055, h1059, h1060, h1063, h915, h999, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1065 | h1065
                                · linarith only [h0, h1059, h1060, h1065, h915, h999, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h1065, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h1062, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1060, h1061, h999, hc01, hc25, hlam, hphi, ht12]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1070 | h1070
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1071 | h1071
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1072 | h1072
                              · linarith only [h0, h1055, h1059, h1060, h1072, h915, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h1059, h1060, h1072, h915, hc23, hc34, hlam, hphi]
                            · linarith only [h1071, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1059, h1070, h915, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h0, h1059, h915, h998, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1058, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1057, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h1054, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h915, h998, hlam]
        · linarith only [h915, h997, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h1083 | h1083
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1084 | h1084
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1085 | h1085
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1086 | h1086
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1087 | h1087
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1088 | h1088
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1089 | h1089
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1090 | h1090
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1091 | h1091
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1092 | h1092
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1093 | h1093
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1094 | h1094
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1095 | h1095
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1096 | h1096
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1097 | h1097
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1098 | h1098
                                    · rcases h0bigk with h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [hlam, p1099_0]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h0, hlam, p1099_0]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h915, hlam, p1099_0]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h915, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1099_1]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h915, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p1099_1]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1099_1]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [hlam, p1099_0]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h0, h1083, h1092, h1095, h1098, h915, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1099_1]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h0, h1083, h1092, h1095, h1098, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1099_1]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        rcases p1099_3 (m.d 0 1) (by simp) with h1109 | h1109
                                        · linarith only [h0, h1109, hlam]
                                        · linarith only [h1084, h1109, hlam]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h1083, h1092, h1095, h1098, hc03, hc45, hlam, hphi, ht0b, ht5b, p1099_1]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h1085, hlam, p1099_0]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [hlam, p1099_0]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h1083, h1091, h1092, h1095, h1098, h915, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1099_1]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        rcases p1099_3 (m.d 0 1) (by simp) with h1116 | h1116
                                        · linarith only [h1116, h915, hlam]
                                        · linarith only [h1084, h1116, hlam]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h1083, hlam, p1099_1]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h1086, hlam, p1099_0]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h1088, hlam, p1099_1]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [hlam, p1099_0]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h0, h1083, h1084, h1093, h1096, h1098, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1099_1]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h1084, hlam, p1099_1]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h1087, hlam, p1099_0]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h1089, hlam, p1099_0]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [h1090, hlam, p1099_0]
                                      · have p1099_0 := h1099c.1
                                        have p1099_1 := h1099c.2.1
                                        have p1099_2 := h1099c.2.2.1
                                        have p1099_3 := h1099c.2.2.2
                                        linarith only [hlam, p1099_0]
                                    · linarith only [h1098, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h1097, hc24, hlam, hphi, ht45, u5elo4]
                                · linarith only [h1095, h1096, hc34, hlam, hphi, ht45, u5elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1132 | h1132
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1133 | h1133
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1134 | h1134
                                    · rcases h0bigk with h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [hlam, p1135_0]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h0, hlam, p1135_0]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h915, hlam, p1135_0]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h1091, h915, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1135_1]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h1091, h915, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1135_1]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1135_1]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [hlam, p1135_0]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h0, h1083, h915, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1135_1]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h0, h1086, h1095, h1132, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1135_1]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        rcases p1135_3 (m.d 0 1) (by simp) with h1145 | h1145
                                        · linarith only [h0, h1145, hlam]
                                        · linarith only [h1084, h1145, hlam]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h1083, h1088, h1095, h1132, h1134, hc03, hc45, hlam, hphi, ht0b, ht5b, p1135_1]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h1085, hlam, p1135_0]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [hlam, p1135_0]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h1088, h1091, h1095, h1132, h1134, h915, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1135_1]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        rcases p1135_3 (m.d 0 1) (by simp) with h1152 | h1152
                                        · linarith only [h1152, h915, hlam]
                                        · linarith only [h1084, h1152, hlam]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h1083, hlam, p1135_1]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h1086, hlam, p1135_0]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h1088, hlam, p1135_1]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [hlam, p1135_0]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h0, h1083, h1084, h1093, h1132, h1134, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1135_1]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h1084, hlam, p1135_1]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h1087, hlam, p1135_0]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h1089, hlam, p1135_0]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [h1090, hlam, p1135_0]
                                      · have p1135_0 := h1135c.1
                                        have p1135_1 := h1135c.2.1
                                        have p1135_2 := h1135c.2.2.1
                                        have p1135_3 := h1135c.2.2.2
                                        linarith only [hlam, p1135_0]
                                    · linarith only [h1095, h1132, h1134, hc35, hlam, hphi, u5elo4]
                                  · linarith only [h1133, hc24, hlam, hphi, ht45, u5elo4]
                                · linarith only [h1132, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h1094, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h1091, h1093, h915, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h1086, h1092, hlam]
                      · linarith only [h0, h1085, h1091, hlam]
                    · linarith only [h1090, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1089, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h1083, h1088, h915, hlam]
              · linarith only [h1083, h1085, h1087, h915, hc14, hlam, hphi, ht45, u5elo2]
            · linarith only [h1083, h1085, h1086, h915, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1177 | h1177
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1178 | h1178
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1179 | h1179
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1180 | h1180
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1181 | h1181
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1182 | h1182
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1183 | h1183
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1184 | h1184
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1185 | h1185
                            · linarith only [h0, h1083, h1085, h1182, h1185, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h1185, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1085, h1182, h1184, hc01, hc25, hlam, hphi, ht12]
                        · linarith only [h0, h1085, h1182, h1183, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1190 | h1190
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1191 | h1191
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1192 | h1192
                            · linarith only [h0, h1083, h1182, h1192, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h1192, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1191, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h1083, h1177, h1190, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h1181, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1180, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h0, h1083, h1085, h1179, hlam]
              · linarith only [h0, h1178, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h1083, h1177, hlam]
        · linarith only [h1083, h1084, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1203 | h1203
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1204 | h1204
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1205 | h1205
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1206 | h1206
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1207 | h1207
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1208 | h1208
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1209 | h1209
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1210 | h1210
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1211 | h1211
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1212 | h1212
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1213 | h1213
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1214 | h1214
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1215 | h1215
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1216 | h1216
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1217 | h1217
                                    · rcases h0bigk with h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h0, hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h915, hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h1083, hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h915, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p1218_1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1218_1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h0, h1204, h1214, h1217, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1218_1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h0, h1083, h1203, h1212, h1215, h1217, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1218_1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        rcases p1218_3 (m.d 0 1) (by simp) with h1228 | h1228
                                        · linarith only [h0, h1228, hlam]
                                        · linarith only [h1203, h1228, hlam]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h1203, h1212, h1215, h1217, hc03, hc45, hlam, hphi, ht0b, ht5b, p1218_1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h1204, hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h1083, h1203, h1210, h1212, h1215, h1217, h915, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1218_1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        rcases p1218_3 (m.d 0 1) (by simp) with h1235 | h1235
                                        · linarith only [h1235, h915, hlam]
                                        · linarith only [h1203, h1235, hlam]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h1203, h1212, h1215, h1217, hc04, hc45, hlam, hphi, ht0b, ht5b, p1218_1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h1205, hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h1207, hlam, p1218_1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        rcases p1218_3 (m.d 0 1) (by simp) with h1242 | h1242
                                        · linarith only [h1083, h1242, hlam]
                                        · linarith only [h1203, h1242, hlam]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h1203, hlam, p1218_1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h1206, hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h1208, hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h1209, hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [hlam, p1218_0]
                                    · linarith only [h1217, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h1203, h1213, h1216, hc24, hlam, hphi, ht45, u5elo0]
                                · linarith only [h1215, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1253 | h1253
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1254 | h1254
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1255 | h1255
                                    · rcases h0bigk with h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [hlam, p1256_0]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [h0, hlam, p1256_0]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [h915, hlam, p1256_0]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [h1083, hlam, p1256_0]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1256_1]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1256_1]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [hlam, p1256_0]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [h0, h1203, h915, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1256_1]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [h0, h1083, h1203, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1256_1]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        rcases p1256_3 (m.d 0 1) (by simp) with h1266 | h1266
                                        · linarith only [h0, h1266, hlam]
                                        · linarith only [h1203, h1266, hlam]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [h1203, h1212, h1253, h1255, hc03, hc45, hlam, hphi, ht0b, ht5b, p1256_1]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [h1204, hlam, p1256_0]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [hlam, p1256_0]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [h1207, h1210, h1214, h1253, h1255, h915, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1256_1]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        rcases p1256_3 (m.d 0 1) (by simp) with h1273 | h1273
                                        · linarith only [h1273, h915, hlam]
                                        · linarith only [h1203, h1273, hlam]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [h1203, h1212, h1253, h1255, hc04, hc45, hlam, hphi, ht0b, ht5b, p1256_1]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [h1205, hlam, p1256_0]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [h1207, hlam, p1256_1]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [hlam, p1256_0]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        rcases p1256_3 (m.d 0 1) (by simp) with h1280 | h1280
                                        · linarith only [h1083, h1280, hlam]
                                        · linarith only [h1203, h1280, hlam]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [h1203, hlam, p1256_1]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [h1206, hlam, p1256_0]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [h1208, hlam, p1256_0]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [h1209, hlam, p1256_0]
                                      · have p1256_0 := h1256c.1
                                        have p1256_1 := h1256c.2.1
                                        have p1256_2 := h1256c.2.2.1
                                        have p1256_3 := h1256c.2.2.2
                                        linarith only [hlam, p1256_0]
                                    · linarith only [h1214, h1253, h1255, hc35, hlam, hphi, u5elo4]
                                  · linarith only [h1203, h1213, h1254, hc24, hlam, hphi, ht45, u5elo0]
                                · linarith only [h1253, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h1213, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1212, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h1203, h1205, h1210, h1211, h915, hc02, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h1204, h1210, hlam]
                    · linarith only [h1083, h1203, h1209, hc15, hlam, hphi, u5elo4]
                  · linarith only [h1207, h1208, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1297 | h1297
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1298 | h1298
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1299 | h1299
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1300 | h1300
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1301 | h1301
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1302 | h1302
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1303 | h1303
                              · linarith only [h1203, h1204, h1207, h1301, h1303, h915, hc02, hc25, hlam, hphi, ht0b, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1305 | h1305
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1306 | h1306
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1307 | h1307
                                    · rcases h0bigk with h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [hlam, p1308_0]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h0, hlam, p1308_0]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h915, hlam, p1308_0]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h1083, hlam, p1308_0]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h915, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p1308_1]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1308_1]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [hlam, p1308_0]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h0, h1203, h1301, h1305, h1307, h915, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1308_1]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h0, h1203, h1207, h1301, h1305, h1307, h915, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1308_1]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        rcases p1308_3 (m.d 0 1) (by simp) with h1318 | h1318
                                        · linarith only [h0, h1318, hlam]
                                        · linarith only [h1203, h1318, hlam]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h1203, h1301, h1305, h1307, hc03, hc45, hlam, hphi, ht0b, ht5b, p1308_1]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h1204, hlam, p1308_0]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [hlam, p1308_0]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h1207, hlam, p1308_0]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h1203, h1207, h1301, h1305, h1307, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1308_1]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h1203, h1207, h1301, h1305, h1307, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1308_1]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h1205, hlam, p1308_0]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h1207, hc03, hc34, hlam, hphi, p1308_1]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [hlam, p1308_0]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        rcases p1308_3 (m.d 0 1) (by simp) with h1330 | h1330
                                        · linarith only [h1083, h1330, hlam]
                                        · linarith only [h1203, h1330, hlam]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h1203, hlam, p1308_1]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h1206, hlam, p1308_0]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h1297, hlam, p1308_0]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [h1298, hlam, p1308_0]
                                      · have p1308_0 := h1308c.1
                                        have p1308_1 := h1308c.2.1
                                        have p1308_2 := h1308c.2.2.1
                                        have p1308_3 := h1308c.2.2.2
                                        linarith only [hlam, p1308_0]
                                    · linarith only [h1207, h1307, hc04, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h1203, h1302, h1306, hc24, hlam, hphi, ht45, u5elo0]
                                · linarith only [h1305, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h1302, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1301, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h1203, h1205, h1299, h1300, h915, hc02, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h1204, h1299, hlam]
                    · linarith only [h1203, h1207, h1298, h915, hc15, hlam, hphi, u5elo4]
                  · linarith only [h1203, h1297, h915, hc15, hlam, hphi, u5elo3]
              · linarith only [h1206, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1348 | h1348
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1349 | h1349
                · linarith only [h1204, h1205, h1349, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1351 | h1351
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1352 | h1352
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1353 | h1353
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1354 | h1354
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1355 | h1355
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1356 | h1356
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1357 | h1357
                              · linarith only [h1204, h1205, h1349, h1354, h1357, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1359 | h1359
                                · linarith only [h1204, h1205, h1354, h1359, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h1359, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h1205, h1354, h1356, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h1355, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1364 | h1364
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1365 | h1365
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1366 | h1366
                              · linarith only [h1203, h1204, h1205, h1349, h1366, h915, hc04, hc15, hlam, hphi, ht0b, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1368 | h1368
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1369 | h1369
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1370 | h1370
                                    · rcases h0bigk with h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [hlam, p1371_0]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h0, hlam, p1371_0]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h915, hlam, p1371_0]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h1083, hlam, p1371_0]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h1353, h1354, h1366, h915, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1371_1]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h1203, hc02, hc15, hlam, hphi, ht0b, ht5b, p1371_1]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [hlam, p1371_0]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h0, h1203, h1354, h1364, h1366, h1368, h1370, h915, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1371_1]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h1205, hlam, p1371_1]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h0, h1203, h1354, h1364, h1366, h1368, h1370, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1371_1]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h1203, h1364, h1368, h1370, hc03, hc45, hlam, hphi, ht0b, ht5b, p1371_1]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h1204, hlam, p1371_0]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [hlam, p1371_0]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h1349, hlam, p1371_0]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h0, h1203, h1204, h1354, h1364, h1366, h1368, h1370, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1371_1]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h1203, h1364, h1368, h1370, hc04, hc45, hlam, hphi, ht0b, ht5b, p1371_1]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h1205, h1366, hc02, hc34, hlam, hphi, ht23, p1371_1]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h1203, h1205, h1364, h1366, h1368, h1370, h915, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1371_1]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [hlam, p1371_0]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        rcases p1371_3 (m.d 0 1) (by simp) with h1391 | h1391
                                        · linarith only [h1083, h1391, hlam]
                                        · linarith only [h1203, h1391, hlam]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h1203, hlam, p1371_1]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h1348, hlam, p1371_0]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h1351, hlam, p1371_0]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [h1352, hlam, p1371_0]
                                      · have p1371_0 := h1371c.1
                                        have p1371_1 := h1371c.2.1
                                        have p1371_2 := h1371c.2.2.1
                                        have p1371_3 := h1371c.2.2.2
                                        linarith only [hlam, p1371_0]
                                    · linarith only [h1354, h1366, h1370, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                                  · linarith only [h1203, h1353, h1354, h1365, h1369, h915, hlam]
                                · linarith only [h1368, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h1365, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h1353, h1364, h915, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h1203, h1204, h1353, hc02, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1352, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1351, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h1348, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1408 | h1408
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1409 | h1409
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1410 | h1410
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1411 | h1411
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1412 | h1412
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1413 | h1413
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1414 | h1414
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1415 | h1415
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1416 | h1416
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1417 | h1417
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1418 | h1418
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1419 | h1419
                                  · linarith only [h1204, h1408, h1413, h1419, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h1419, hc24, hlam, hphi, ht45, u5elo4]
                                · linarith only [h1204, h1418, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                              · linarith only [h1083, h1203, h1204, h1408, h1410, h1417, hc03, hc15, hlam, hphi, ht0b, ht5b]
                            · linarith only [h1083, h1203, h1415, h1416, hc25, hlam, hphi, u5elo4]
                          · linarith only [h1204, h1413, h1415, hc03, hlam, hphi, ht34, ht45, u5elo2]
                        · linarith only [h1204, h1413, h1414, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1427 | h1427
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1428 | h1428
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1429 | h1429
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1430 | h1430
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1431 | h1431
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1432 | h1432
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1433 | h1433
                                    · rcases h0bigk with h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [hlam, p1434_0]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h0, hlam, p1434_0]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h915, hlam, p1434_0]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h1083, hlam, p1434_0]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h1083, h1413, h1427, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1434_1]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h0, h1413, hc01, hc23, hlam, hphi, ht12, p1434_1]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [hlam, p1434_0]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h1204, hlam, p1434_1]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h0, h1413, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1434_1]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h0, h1203, h1413, h1428, h1431, h1433, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1434_1]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h1203, h1428, h1431, h1433, hc03, hc45, hlam, hphi, ht0b, ht5b, p1434_1]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h1204, hc02, hc23, hlam, hphi, p1434_1]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [hlam, p1434_0]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h1083, h1203, h1204, h1428, h1431, h1433, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1434_1]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        rcases p1434_3 (m.d 0 1) (by simp) with h1449 | h1449
                                        · linarith only [h1449, h915, hlam]
                                        · linarith only [h1203, h1449, hlam]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h1203, h1428, h1431, h1433, hc04, hc45, hlam, hphi, ht0b, ht5b, p1434_1]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h1408, hlam, p1434_0]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h1410, hlam, p1434_1]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [hlam, p1434_0]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h1083, h1203, h1413, h1427, h1428, h1431, h1433, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1434_1]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h1203, hlam, p1434_1]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h1409, hlam, p1434_0]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h1411, hlam, p1434_0]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [h1412, hlam, p1434_0]
                                      · have p1434_0 := h1434c.1
                                        have p1434_1 := h1434c.2.1
                                        have p1434_2 := h1434c.2.2.1
                                        have p1434_3 := h1434c.2.2.2
                                        linarith only [hlam, p1434_0]
                                    · linarith only [h1433, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h1203, h1429, h1432, hc24, hlam, hphi, ht45, u5elo0]
                                · linarith only [h1083, h1413, h1427, h1431, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h1083, h1203, h1413, h1427, h1429, h1430, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1083, h1203, h1428, h1429, hc25, hlam, hphi, u5elo4]
                          · linarith only [h1083, h1427, h1428, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h1408, h1427, hlam]
                    · linarith only [h1412, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1411, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h1204, h1408, h1410, hlam]
              · linarith only [h1409, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1473 | h1473
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1474 | h1474
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1475 | h1475
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1476 | h1476
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1477 | h1477
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1478 | h1478
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1479 | h1479
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1480 | h1480
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1481 | h1481
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1482 | h1482
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1483 | h1483
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1484 | h1484
                                    · rcases h0bigk with h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [hlam, p1485_0]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h0, hlam, p1485_0]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h915, hlam, p1485_0]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h1083, hlam, p1485_0]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h0, h1408, h1477, h1481, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1485_1]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h1408, h1477, h1481, hc01, hc12, hlam, hphi, p1485_1]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [hlam, p1485_0]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h1204, hlam, p1485_1]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h1408, hlam, p1485_1]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h1203, h1408, h1477, h1479, h1481, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1485_1]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h1203, h1479, hc03, hc25, hlam, hphi, ht0b, ht5b, p1485_1]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h1204, h1477, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1485_1]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [hlam, p1485_0]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h0, h1203, h1204, h1408, h1477, h1479, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1485_1]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h1203, h1204, h1477, h1479, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1485_1]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h1203, h1479, hc04, hc25, hlam, hphi, ht0b, ht5b, p1485_1]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h0, h1203, h1408, h1477, h1479, h1481, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1485_1]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h1474, hlam, p1485_1]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [hlam, p1485_0]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h1203, h1408, h1477, h1479, h1481, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1485_1]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h1203, hlam, p1485_1]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h1473, hlam, p1485_0]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h1475, hlam, p1485_0]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [h1476, hlam, p1485_0]
                                      · have p1485_0 := h1485c.1
                                        have p1485_1 := h1485c.2.1
                                        have p1485_2 := h1485c.2.2.1
                                        have p1485_3 := h1485c.2.2.2
                                        linarith only [hlam, p1485_0]
                                    · linarith only [h1484, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h1203, h1408, h1480, h1483, hc04, hlam, hphi, ht45, u5elo0]
                                · linarith only [h0, h1408, h1481, h1482, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                              · linarith only [h0, h1203, h1204, h1474, h1480, h1481, hc03, hc45, hlam, hphi, ht0b, ht5b]
                            · linarith only [h1480, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1204, h1477, h1479, hc01, hc25, hlam, hphi, ht12]
                        · linarith only [h0, h1203, h1204, h1477, h1478, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1518 | h1518
                        · linarith only [h0, h1203, h1408, h1477, h1518, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1520 | h1520
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1521 | h1521
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1522 | h1522
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1523 | h1523
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1524 | h1524
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1525 | h1525
                                    · rcases h0bigk with h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [hlam, p1526_0]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h0, hlam, p1526_0]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h915, hlam, p1526_0]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h1083, hlam, p1526_0]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h0, h1518, h1522, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1526_1]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h0, h1518, h1522, hc01, hc23, hlam, hphi, ht12, p1526_1]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [hlam, p1526_0]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h1204, hlam, p1526_1]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h1408, hlam, p1526_1]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h0, h1203, h1518, h1520, h1522, h1523, h1525, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1526_1]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h1203, h1477, h1520, h1523, h1525, h915, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1526_1]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h1477, h915, hc02, hc23, hlam, hphi, p1526_1]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [hlam, p1526_0]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h1083, h1203, h1477, h1520, h1523, h1525, h915, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1526_1]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        rcases p1526_3 (m.d 0 1) (by simp) with h1541 | h1541
                                        · linarith only [h1541, h915, hlam]
                                        · linarith only [h1203, h1541, hlam]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h1203, h1520, h1523, h1525, hc04, hc45, hlam, hphi, ht0b, ht5b, p1526_1]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h0, h1203, h1408, h1520, h1522, h1523, h1525, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1526_1]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h1474, hlam, p1526_1]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [hlam, p1526_0]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        rcases p1526_3 (m.d 0 1) (by simp) with h1548 | h1548
                                        · linarith only [h1083, h1548, hlam]
                                        · linarith only [h1203, h1548, hlam]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h1203, hlam, p1526_1]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h1473, hlam, p1526_0]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h1475, hlam, p1526_0]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [h1476, hlam, p1526_0]
                                      · have p1526_0 := h1526c.1
                                        have p1526_1 := h1526c.2.1
                                        have p1526_2 := h1526c.2.2.1
                                        have p1526_3 := h1526c.2.2.2
                                        linarith only [hlam, p1526_0]
                                    · linarith only [h1525, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h0, h1203, h1518, h1521, h1524, hlam]
                                · linarith only [h0, h1518, h1522, h1523, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h1203, h1477, h1520, h1522, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1521, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1203, h1520, hc15, hlam, hphi, u5elo2]
                    · linarith only [h1476, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1475, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1564 | h1564
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1565 | h1565
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1566 | h1566
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1567 | h1567
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1568 | h1568
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1569 | h1569
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1570 | h1570
                              · linarith only [h0, h1203, h1204, h1474, h1566, h1568, h1570, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1572 | h1572
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1573 | h1573
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1574 | h1574
                                    · rcases h0bigk with h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [hlam, p1575_0]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h0, hlam, p1575_0]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h915, hlam, p1575_0]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h1083, hlam, p1575_0]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h0, h1204, h1567, h1570, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p1575_1]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h1204, h1567, h1570, hc01, hc14, hlam, hphi, p1575_1]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [hlam, p1575_0]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h1204, hlam, p1575_1]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h1408, hlam, p1575_1]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h1203, h1204, h1567, h1568, h1570, h1572, h1574, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1575_1]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h1203, h1568, h1572, h1574, hc03, hc45, hlam, hphi, ht0b, ht5b, p1575_1]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h1204, hc02, hc23, hlam, hphi, p1575_1]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [hlam, p1575_0]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h1474, hlam, p1575_0]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h1203, h1474, h1568, h1572, h1574, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1575_1]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h1203, h1474, h1568, h1572, h1574, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1575_1]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h0, h1203, h1474, h1568, h1572, h1574, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1575_1]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h1474, hc03, hc34, hlam, hphi, p1575_1]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [hlam, p1575_0]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h1203, h1408, h1567, h1568, h1572, h1574, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1575_1]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h1203, hlam, p1575_1]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h1473, hlam, p1575_0]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h1564, hlam, p1575_0]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [h1565, hlam, p1575_0]
                                      · have p1575_0 := h1575c.1
                                        have p1575_1 := h1575c.2.1
                                        have p1575_2 := h1575c.2.2.1
                                        have p1575_3 := h1575c.2.2.2
                                        linarith only [hlam, p1575_0]
                                    · linarith only [h1570, h1574, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                  · linarith only [h0, h1203, h1204, h1408, h1569, h1570, h1573, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                · linarith only [h0, h1204, h1572, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                            · linarith only [h1569, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1204, h1566, h1568, hc01, hc25, hlam, hphi, ht12]
                        · linarith only [h0, h1204, h1566, h1567, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1607 | h1607
                        · linarith only [h0, h1203, h1408, h1566, h1607, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1609 | h1609
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1610 | h1610
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1611 | h1611
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1612 | h1612
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1613 | h1613
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1614 | h1614
                                    · rcases h0bigk with h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [hlam, p1615_0]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h0, hlam, p1615_0]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h915, hlam, p1615_0]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h1083, hlam, p1615_0]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h0, h1607, h1611, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1615_1]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h0, h1607, h1611, hc01, hc23, hlam, hphi, ht12, p1615_1]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [hlam, p1615_0]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h1204, hlam, p1615_1]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h1408, hlam, p1615_1]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h1203, h1204, h1474, h1609, h1611, h1612, h1614, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1615_1]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h1203, h1474, h1609, h1611, h1612, h1614, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1615_1]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h1474, h1611, hc02, hc23, hlam, hphi, p1615_1]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [hlam, p1615_0]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h1474, hlam, p1615_0]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h1203, h1474, h1609, h1611, h1612, h1614, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1615_1]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h1203, h1474, h1609, h1611, h1612, h1614, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1615_1]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h0, h1203, h1474, h1609, h1611, h1612, h1614, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1615_1]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h1474, h1611, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1615_1]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [hlam, p1615_0]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h1203, h1474, h1609, h1611, h1612, h1614, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1615_1]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h1203, hlam, p1615_1]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h1473, hlam, p1615_0]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h1564, hlam, p1615_0]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [h1565, hlam, p1615_0]
                                      · have p1615_0 := h1615c.1
                                        have p1615_1 := h1615c.2.1
                                        have p1615_2 := h1615c.2.2.1
                                        have p1615_3 := h1615c.2.2.2
                                        linarith only [hlam, p1615_0]
                                    · linarith only [h1474, h1614, hc04, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h0, h1203, h1607, h1610, h1613, hlam]
                                · linarith only [h0, h1204, h1474, h1611, h1612, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h1566, h1611, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1610, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1203, h1609, hc15, hlam, hphi, u5elo2]
                    · linarith only [h1565, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1204, h1564, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h1203, h1473, hc15, hlam, hphi, u5elo2]
        · linarith only [h1203, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem n7l_sBT2_H_L_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h5bigk := hb5.1
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h3, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h12, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h15 | h15
                  · linarith only [h15, h6, h7, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h17, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h17, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h20 | h20
                · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
                    · linarith only [h0, h22, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h22, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h20, h21, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                    · linarith only [h0, h27, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h27, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
                    · linarith only [h0, h30, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h3, h30, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h33 | h33
              · rcases m.htr 0 3 5 (by decide) (by decide) with h34 | h34
                · linarith only [h3, h34, h5, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h36 | h36
                  · linarith only [h3, h33, h36, h5, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
                    · linarith only [h0, h38, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h3, h38, h5, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h41 | h41
                · linarith only [h33, h4, h41, h5, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h43 | h43
                  · linarith only [h4, h43, h5, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
                    · linarith only [h0, h45, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h3, h45, h5, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h48 | h48
            · rcases m.htr 0 3 4 (by decide) (by decide) with h49 | h49
              · linarith only [h3, h4, h49, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h51 | h51
                · rcases m.htr 0 4 5 (by decide) (by decide) with h52 | h52
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
                    · linarith only [h0, h53, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h3, h53, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h3, h4, h51, h52, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h57 | h57
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
                    · linarith only [h0, h58, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h3, h4, h58, hc12, hlam, hphi, u2elo3]
                  · linarith only [h4, h48, h57, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h62 | h62
              · linarith only [h3, h4, h62, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h64 | h64
                · linarith only [h3, h48, h64, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h66 | h66
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h67 | h67
                    · linarith only [h0, h67, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h3, h4, h67, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h70 | h70
                    · linarith only [h0, h70, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h3, h4, h70, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h73 | h73
          · rcases m.htr 0 2 5 (by decide) (by decide) with h74 | h74
            · rcases m.htr 0 3 4 (by decide) (by decide) with h75 | h75
              · rcases m.htr 0 3 5 (by decide) (by decide) with h76 | h76
                · rcases m.htr 0 4 5 (by decide) (by decide) with h77 | h77
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
                    · linarith only [h3, h78, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h80 | h80
                      · linarith only [h0, h80, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h73, h80, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h83 | h83
                    · linarith only [h3, h83, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
                      · linarith only [h0, h85, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h73, h85, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h3, h74, h76, hlam]
              · linarith only [h3, h73, h75, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h90 | h90
              · rcases m.htr 0 3 5 (by decide) (by decide) with h91 | h91
                · rcases m.htr 0 4 5 (by decide) (by decide) with h92 | h92
                  · linarith only [h73, h74, h92, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
                    · linarith only [h0, h94, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h96 | h96
                      · linarith only [h0, h96, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h73, h96, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h99 | h99
                  · linarith only [h3, h73, h91, h99, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
                    · linarith only [h0, h101, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                      · linarith only [h0, h103, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h103, h2, h3, h73, h91, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · linarith only [h3, h73, h90, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h107 | h107
            · rcases m.htr 0 3 4 (by decide) (by decide) with h108 | h108
              · rcases m.htr 0 3 5 (by decide) (by decide) with h109 | h109
                · rcases m.htr 0 4 5 (by decide) (by decide) with h110 | h110
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
                    · linarith only [h111, h3, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
                      · linarith only [h0, h107, h113, h73, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h115 | h115
                        · linarith only [h1, h113, h115, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h107, h115, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h107, h110, h73, hlam]
                · linarith only [h107, h108, h109, h73, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h120 | h120
                · rcases m.htr 0 4 5 (by decide) (by decide) with h121 | h121
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                    · linarith only [h0, h122, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
                      · linarith only [h0, h124, h73, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h126 | h126
                        · linarith only [h1, h124, h126, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h107, h126, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h107, h108, h121, h3, hlam]
                · linarith only [h107, h120, h3, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h131 | h131
              · rcases m.htr 0 3 5 (by decide) (by decide) with h132 | h132
                · rcases m.htr 0 4 5 (by decide) (by decide) with h133 | h133
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h134 | h134
                    · linarith only [h134, h3, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
                      · linarith only [h0, h136, h73, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h138 | h138
                        · linarith only [h0, h107, h138, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h140 | h140
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h141 | h141
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h142 | h142
                              · linarith only [h1, h142, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h131, h133, h142, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h132, h141, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h131, h134, h140, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h147 | h147
                    · linarith only [h147, h3, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h149 | h149
                      · linarith only [h0, h149, h73, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h151 | h151
                        · linarith only [h0, h107, h151, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h153 | h153
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h154 | h154
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h155 | h155
                              · linarith only [h1, h133, h155, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h157 | h157
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h158 | h158
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h159 | h159
                                    · linarith only [h0, h133, h159, h73, hc12, hlam, hphi, u2elo3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h161 | h161
                                      · linarith only [h0, h153, h159, h161, h73, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                      · rcases h5bigk with h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [hlam, p163_0]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h2, hc15, hlam, hphi, ht0b, ht5b, p163_1, u0elo0]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h107, hlam, p163_0]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h2, hc35, hlam, hphi, ht0b, ht5b, p163_1, u0elo0]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h133, hlam, p163_1]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h2, hlam, p163_0]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [hlam, p163_0]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h151, hlam, p163_0]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h2, hc35, hlam, hphi, ht0b, ht5b, p163_1, u0elo0]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h155, hlam, p163_1]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h158, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p163_1, u2elo2]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h158, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p163_1, u2elo2]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [hlam, p163_0]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h158, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p163_1, u2elo2]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h159, hlam, p163_1]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h132, hlam, p163_1]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h154, hlam, p163_1]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h158, hlam, p163_0]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [hlam, p163_0]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h161, hlam, p163_1]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h0, h133, h73, hc12, hc45, hlam, hphi, ht23, ht34, p163_1]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h149, h155, hc12, hc45, hlam, hphi, ht23, ht34, p163_1]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h0, h107, hc12, hc45, hlam, hphi, ht23, ht34, p163_1]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [h161, hc34, hc45, hlam, hphi, p163_1]
                                        · have p163_0 := h163c.1
                                          have p163_1 := h163c.2.1
                                          have p163_2 := h163c.2.2.1
                                          have p163_3 := h163c.2.2.2
                                          linarith only [hlam, p163_0]
                                  · linarith only [h132, h158, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h0, h131, h157, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h132, h153, h154, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                          · linarith only [h131, h153, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h193 | h193
                  · linarith only [h131, h132, h193, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
                    · linarith only [h0, h131, h195, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h197 | h197
                      · linarith only [h0, h197, h73, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h199 | h199
                        · linarith only [h0, h107, h199, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h201 | h201
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h202 | h202
                            · linarith only [h131, h132, h195, h202, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · linarith only [h2, h201, h202, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h131, h195, h201, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h206 | h206
                · rcases m.htr 0 4 5 (by decide) (by decide) with h207 | h207
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h208 | h208
                    · linarith only [h0, h208, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h210 | h210
                      · linarith only [h0, h210, h73, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h212 | h212
                        · linarith only [h0, h107, h212, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h214 | h214
                          · linarith only [h131, h206, h208, h214, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h216 | h216
                            · linarith only [h1, h214, h216, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h206, h208, h216, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h131, h206, h207, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h220 | h220
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h221 | h221
                    · linarith only [h0, h221, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h223 | h223
                      · linarith only [h0, h223, h73, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h225 | h225
                        · linarith only [h0, h107, h225, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h227 | h227
                          · linarith only [h131, h221, h227, h3, hc02, hlam, hphi, u2elo2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h229 | h229
                            · linarith only [h0, h1, h206, h227, h229, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h231 | h231
                              · linarith only [h1, h231, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h1, h220, h227, h231, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h234 | h234
                    · linarith only [h0, h234, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h236 | h236
                      · linarith only [h0, h236, h73, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h238 | h238
                        · linarith only [h0, h107, h238, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h240 | h240
                          · linarith only [h131, h234, h240, h3, hc02, hlam, hphi, u2elo2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h242 | h242
                            · linarith only [h0, h1, h206, h240, h242, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h244 | h244
                              · linarith only [h1, h220, h244, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h246 | h246
                                · linarith only [h0, h131, h246, h3, hc12, hlam, hphi, u2elo2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h248 | h248
                                  · linarith only [h0, h206, h246, h248, h3, hc12, hc34, hlam, hphi, ht23]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h250 | h250
                                    · linarith only [h0, h131, h220, h250, h3, hc12, hlam, hphi, u2elo3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h252 | h252
                                      · linarith only [h0, h246, h250, h252, h3, hc12, hc34, hlam, hphi, ht23]
                                      · linarith only [h0, h246, h252, h3, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h255 | h255
        · rcases m.htr 0 2 4 (by decide) (by decide) with h256 | h256
          · rcases m.htr 0 2 5 (by decide) (by decide) with h257 | h257
            · linarith only [h0, h2, h257, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h259 | h259
              · rcases m.htr 0 3 5 (by decide) (by decide) with h260 | h260
                · linarith only [h0, h2, h255, h260, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h262 | h262
                  · linarith only [h1, h2, h262, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h264 | h264
                    · linarith only [h0, h264, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h255, h257, h264, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h267 | h267
                · linarith only [h0, h2, h256, h257, h259, h267, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h269 | h269
                  · linarith only [h0, h2, h256, h257, h269, hc12, hlam, hphi, u2elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h271 | h271
                    · linarith only [h0, h271, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h255, h271, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h274 | h274
            · linarith only [h1, h2, h256, h274, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h276 | h276
              · linarith only [h255, h256, h276, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h278 | h278
                · linarith only [h1, h2, h255, h256, h278, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h280 | h280
                  · linarith only [h1, h2, h280, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h282 | h282
                    · linarith only [h0, h2, h282, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h255, h256, h282, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h285 | h285
          · rcases m.htr 0 2 5 (by decide) (by decide) with h286 | h286
            · linarith only [h0, h2, h255, h286, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h288 | h288
              · rcases m.htr 0 3 5 (by decide) (by decide) with h289 | h289
                · rcases m.htr 0 4 5 (by decide) (by decide) with h290 | h290
                  · linarith only [h0, h2, h255, h285, h290, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h292 | h292
                    · linarith only [h0, h255, h292, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h294 | h294
                      · linarith only [h0, h2, h289, h294, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h285, h294, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h297 | h297
                  · linarith only [h0, h2, h285, h286, h297, hc12, hlam, hphi, u2elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h299 | h299
                    · linarith only [h0, h299, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h301 | h301
                      · linarith only [h0, h2, h301, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · linarith only [h285, h286, h301, hc12, hlam, hphi, u2elo4]
              · linarith only [h255, h285, h288, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h305 | h305
            · linarith only [h0, h2, h285, h305, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h307 | h307
              · rcases m.htr 0 3 5 (by decide) (by decide) with h308 | h308
                · rcases m.htr 0 4 5 (by decide) (by decide) with h309 | h309
                  · linarith only [h1, h2, h309, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h311 | h311
                    · linarith only [h0, h311, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h313 | h313
                      · linarith only [h0, h2, h308, h313, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h315 | h315
                        · linarith only [h1, h2, h305, h308, h313, h315, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h2, h315, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h318 | h318
                  · linarith only [h1, h2, h318, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h320 | h320
                    · linarith only [h0, h255, h320, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h322 | h322
                      · linarith only [h0, h285, h322, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h324 | h324
                        · linarith only [h1, h2, h322, h324, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                        · linarith only [h1, h2, h322, h324, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h327 | h327
                · linarith only [h1, h2, h307, h327, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h329 | h329
                  · linarith only [h1, h2, h329, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h331 | h331
                    · linarith only [h0, h255, h331, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h333 | h333
                      · linarith only [h0, h285, h333, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h335 | h335
                        · linarith only [h0, h2, h335, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                        · linarith only [h1, h2, h333, h335, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h338 | h338
      · rcases m.htr 0 2 3 (by decide) (by decide) with h339 | h339
        · rcases m.htr 0 2 4 (by decide) (by decide) with h340 | h340
          · linarith only [h0, h1, h340, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h342 | h342
            · rcases m.htr 0 3 4 (by decide) (by decide) with h343 | h343
              · linarith only [h0, h1, h339, h343, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h345 | h345
                · rcases m.htr 0 4 5 (by decide) (by decide) with h346 | h346
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h347 | h347
                    · linarith only [h0, h1, h347, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h1, h339, h347, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1, h339, h345, h346, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h351 | h351
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h352 | h352
                    · linarith only [h0, h1, h352, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h339, h340, h352, hc12, hlam, hphi, u2elo3]
                  · linarith only [h0, h1, h342, h351, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h356 | h356
              · linarith only [h1, h338, h339, h342, h356, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h358 | h358
                · linarith only [h339, h342, h358, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h360 | h360
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h361 | h361
                    · linarith only [h0, h1, h361, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h339, h340, h361, hc12, hlam, hphi, u2elo3]
                  · linarith only [h1, h338, h360, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h365 | h365
          · linarith only [h0, h1, h339, h365, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h367 | h367
            · rcases m.htr 0 3 4 (by decide) (by decide) with h368 | h368
              · rcases m.htr 0 3 5 (by decide) (by decide) with h369 | h369
                · rcases m.htr 0 4 5 (by decide) (by decide) with h370 | h370
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h371 | h371
                    · linarith only [h0, h339, h371, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h373 | h373
                      · linarith only [h0, h1, h365, h367, h368, h373, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h0, h1, h373, hc12, hlam, hphi, u2elo3]
                  · linarith only [h0, h1, h339, h367, h370, hc12, hlam, hphi, u2elo2]
                · linarith only [h339, h367, h369, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h378 | h378
                · rcases m.htr 0 4 5 (by decide) (by decide) with h379 | h379
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h380 | h380
                    · linarith only [h0, h339, h380, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h382 | h382
                      · linarith only [h0, h1, h382, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h0, h1, h382, hc12, hlam, hphi, u2elo3]
                  · linarith only [h0, h1, h339, h367, h379, hc12, hlam, hphi, u2elo2]
                · linarith only [h339, h367, h378, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h387 | h387
              · rcases m.htr 0 3 5 (by decide) (by decide) with h388 | h388
                · rcases m.htr 0 4 5 (by decide) (by decide) with h389 | h389
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h390 | h390
                    · linarith only [h0, h339, h390, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h392 | h392
                      · linarith only [h0, h1, h387, h392, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1, h392, hc12, hlam, hphi, u2elo3]
                  · linarith only [h1, h338, h389, hlam]
                · linarith only [h1, h338, h387, h388, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h397 | h397
                · rcases m.htr 0 4 5 (by decide) (by decide) with h398 | h398
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h399 | h399
                    · linarith only [h0, h339, h399, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h401 | h401
                      · linarith only [h0, h1, h401, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h0, h1, h401, hc12, hlam, hphi, u2elo3]
                  · linarith only [h1, h338, h398, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h405 | h405
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h406 | h406
                    · linarith only [h0, h339, h406, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h408 | h408
                      · linarith only [h0, h1, h408, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h0, h1, h408, hc12, hlam, hphi, u2elo3]
                  · linarith only [h1, h338, h405, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h412 | h412
        · rcases m.htr 0 2 4 (by decide) (by decide) with h413 | h413
          · linarith only [h0, h1, h413, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h415 | h415
            · linarith only [h0, h338, h415, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h417 | h417
              · linarith only [h0, h1, h412, h417, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h419 | h419
                · linarith only [h0, h338, h412, h419, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h421 | h421
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h422 | h422
                    · linarith only [h0, h422, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h338, h412, h421, h422, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h425 | h425
                    · linarith only [h0, h425, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h412, h413, h425, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h428 | h428
          · linarith only [h0, h1, h412, h428, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h430 | h430
            · linarith only [h0, h338, h412, h430, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h432 | h432
              · rcases m.htr 0 3 5 (by decide) (by decide) with h433 | h433
                · rcases m.htr 0 4 5 (by decide) (by decide) with h434 | h434
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h435 | h435
                    · linarith only [h0, h338, h412, h432, h434, h435, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h437 | h437
                      · linarith only [h0, h428, h434, h437, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                      · linarith only [h0, h1, h437, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h440 | h440
                    · linarith only [h0, h412, h440, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h442 | h442
                      · linarith only [h0, h1, h433, h434, h442, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1, h442, hc12, hlam, hphi, u2elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h445 | h445
                  · linarith only [h432, h433, h445, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h447 | h447
                    · linarith only [h0, h1, h412, h432, h447, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h449 | h449
                      · linarith only [h0, h449, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h449, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h452 | h452
                · rcases m.htr 0 4 5 (by decide) (by decide) with h453 | h453
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h454 | h454
                    · linarith only [h0, h412, h454, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h456 | h456
                      · linarith only [h0, h338, h432, h452, h456, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h0, h1, h456, hc12, hlam, hphi, u2elo3]
                  · linarith only [h432, h452, h453, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h460 | h460
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h461 | h461
                    · linarith only [h0, h412, h461, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h463 | h463
                      · linarith only [h0, h338, h460, h463, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h0, h1, h463, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h466 | h466
                    · linarith only [h0, h412, h466, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h468 | h468
                      · linarith only [h0, h468, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h468, hc12, hlam, hphi, u2elo3]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h471 | h471
    · rcases m.htr 0 1 5 (by decide) (by decide) with h472 | h472
      · rcases m.htr 0 2 3 (by decide) (by decide) with h473 | h473
        · rcases m.htr 0 2 4 (by decide) (by decide) with h474 | h474
          · rcases m.htr 0 2 5 (by decide) (by decide) with h475 | h475
            · rcases m.htr 0 3 4 (by decide) (by decide) with h476 | h476
              · rcases m.htr 0 3 5 (by decide) (by decide) with h477 | h477
                · rcases m.htr 0 4 5 (by decide) (by decide) with h478 | h478
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h479 | h479
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h480 | h480
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h481 | h481
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h482 | h482
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h483 | h483
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h484 | h484
                              · linarith only [h471, h484, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h0, h471, h478, h484, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h477, h482, h483, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h473, h476, h482, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h481, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h471, h480, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h471, h473, h479, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h492 | h492
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h493 | h493
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h494 | h494
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h495 | h495
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h496 | h496
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h497 | h497
                              · linarith only [h0, h471, h478, h497, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h499 | h499
                                · linarith only [h473, h499, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h473, h476, h499, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h473, h477, h496, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h473, h476, h492, h495, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h494, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h471, h493, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h471, h492, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h507 | h507
                  · linarith only [h476, h477, h507, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h509 | h509
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h510 | h510
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h511 | h511
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h512 | h512
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h513 | h513
                            · linarith only [h476, h477, h509, h513, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h0, h472, h512, h513, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h476, h512, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h511, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h472, h476, h477, h510, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h472, h476, h477, h509, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h520 | h520
                · rcases m.htr 0 4 5 (by decide) (by decide) with h521 | h521
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h522 | h522
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h523 | h523
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h524 | h524
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h525 | h525
                          · linarith only [h476, h520, h522, h525, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h527 | h527
                            · linarith only [h0, h471, h525, h527, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h520, h527, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h524, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h471, h476, h520, h523, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h0, h471, h476, h520, h522, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h476, h520, h521, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h534 | h534
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h535 | h535
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h536 | h536
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h537 | h537
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h538 | h538
                          · linarith only [h471, h476, h538, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h540 | h540
                            · linarith only [h473, h520, h538, h540, hc23, hc34, hlam, hphi]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h542 | h542
                              · linarith only [h0, h471, h542, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · linarith only [h534, h538, h542, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h0, h537, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h471, h536, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h471, h473, h535, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h548 | h548
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h549 | h549
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h550 | h550
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h551 | h551
                          · linarith only [h471, h476, h551, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h553 | h553
                            · linarith only [h0, h471, h520, h534, h551, h553, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h555 | h555
                              · linarith only [h0, h471, h555, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h557 | h557
                                · linarith only [h473, h557, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h559 | h559
                                  · linarith only [h473, h520, h559, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h561 | h561
                                    · linarith only [h474, h534, h561, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h563 | h563
                                      · rcases h5bigk with h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [hlam, p564_0]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h548, h551, h555, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p564_1, u0elo4]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h0, h472, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p564_1, u2elo1]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h520, hlam, p564_0]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h534, hlam, p564_1]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h472, hlam, p564_0]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [hlam, p564_0]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h0, h472, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p564_1, u2elo1]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h553, hlam, p564_0]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h555, hlam, p564_1]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h475, hlam, p564_1]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h550, hlam, p564_1]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [hlam, p564_0]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h559, hlam, p564_1]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h561, hlam, p564_1]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h472, h548, h551, h555, hc23, hc35, hlam, hphi, p564_1]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h548, h551, h555, hc23, hc35, hlam, hphi, p564_1]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h559, hc23, hc35, hlam, hphi, p564_1]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [hlam, p564_0]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h471, h534, h548, h551, h563, hc23, hc34, hlam, hphi, p564_1]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h472, h548, h551, h555, hc23, hc45, hlam, hphi, ht34, p564_1]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h548, h551, h555, hc23, hc45, hlam, hphi, ht34, p564_1]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h557, h561, hc23, hc45, hlam, hphi, ht34, p564_1]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [h563, hlam, p564_0]
                                        · have p564_0 := h564c.1
                                          have p564_1 := h564c.2.1
                                          have p564_2 := h564c.2.2.1
                                          have p564_3 := h564c.2.2.2
                                          linarith only [hlam, p564_0]
                                      · rcases h5bigk with h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [hlam, p590_0]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h548, h551, h555, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p590_1, u0elo4]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h0, h472, h557, h561, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p590_1, u2elo1]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h520, hlam, p590_0]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h534, hlam, p590_1]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h472, hlam, p590_0]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [hlam, p590_0]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h0, h472, h557, h561, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p590_1, u2elo1]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h553, hlam, p590_0]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h555, hlam, p590_1]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h475, hlam, p590_1]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h550, hlam, p590_1]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [hlam, p590_0]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h559, hlam, p590_1]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h561, hlam, p590_1]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h475, h557, h561, h563, hc23, hc45, hlam, hphi, ht34, p590_1]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h550, h557, h561, h563, hc23, hc45, hlam, hphi, ht34, p590_1]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h557, h561, h563, hc23, hc45, hlam, hphi, ht34, p590_1]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [hlam, p590_0]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h563, hlam, p590_1]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h471, h534, h548, h551, hc23, hc45, hlam, hphi, ht34, p590_1]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h550, h557, h561, hc23, hc45, hlam, hphi, ht34, p590_1]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h557, h561, hc23, hc45, hlam, hphi, ht34, p590_1]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [h473, h520, hc23, hc45, hlam, hphi, ht34, p590_1]
                                        · have p590_0 := h590c.1
                                          have p590_1 := h590c.2.1
                                          have p590_2 := h590c.2.2.1
                                          have p590_3 := h590c.2.2.2
                                          linarith only [hlam, p590_0]
                        · linarith only [h0, h550, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h471, h474, h549, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h0, h471, h473, h548, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · linarith only [h0, h472, h475, hlam]
          · linarith only [h0, h471, h474, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h621 | h621
          · rcases m.htr 0 2 5 (by decide) (by decide) with h622 | h622
            · rcases m.htr 0 3 4 (by decide) (by decide) with h623 | h623
              · rcases m.htr 0 3 5 (by decide) (by decide) with h624 | h624
                · rcases m.htr 0 4 5 (by decide) (by decide) with h625 | h625
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h626 | h626
                    · linarith only [h0, h471, h473, h626, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h471, h626, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h629 | h629
                    · linarith only [h0, h471, h473, h629, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h471, h629, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h0, h472, h473, h624, hlam]
              · linarith only [h0, h471, h473, h623, hlam]
            · linarith only [h0, h472, h622, hlam]
          · linarith only [h0, h471, h621, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h636 | h636
        · rcases m.htr 0 2 4 (by decide) (by decide) with h637 | h637
          · rcases m.htr 0 2 5 (by decide) (by decide) with h638 | h638
            · rcases m.htr 0 3 4 (by decide) (by decide) with h639 | h639
              · rcases m.htr 0 3 5 (by decide) (by decide) with h640 | h640
                · rcases m.htr 0 4 5 (by decide) (by decide) with h641 | h641
                  · linarith only [h471, h472, h641, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h643 | h643
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h644 | h644
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h645 | h645
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h646 | h646
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h647 | h647
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h648 | h648
                              · linarith only [h471, h641, h648, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h650 | h650
                                · linarith only [h636, h650, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h636, h639, h650, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h636, h640, h647, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h636, h639, h643, h646, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h638, h645, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h644, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h471, h643, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h658 | h658
                  · linarith only [h471, h472, h658, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h660 | h660
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h661 | h661
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h662 | h662
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h663 | h663
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h664 | h664
                            · linarith only [h639, h640, h660, h664, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h666 | h666
                              · linarith only [h471, h472, h658, h662, h666, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h668 | h668
                                · linarith only [h636, h668, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h639, h668, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h639, h663, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h638, h662, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h471, h661, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h471, h660, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h675 | h675
                · linarith only [h471, h472, h639, h675, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h677 | h677
                  · linarith only [h471, h472, h677, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h679 | h679
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h680 | h680
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h681 | h681
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h682 | h682
                          · linarith only [h471, h639, h682, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h684 | h684
                            · linarith only [h471, h472, h675, h681, h682, h684, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h686 | h686
                              · linarith only [h471, h472, h681, h686, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h688 | h688
                                · linarith only [h636, h639, h688, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h690 | h690
                                  · linarith only [h471, h472, h679, h682, h684, h690, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h692 | h692
                                    · linarith only [h472, h686, h692, hc01, hlam, hphi, ht12, u2elo3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h694 | h694
                                      · linarith only [h471, h472, h679, h682, h686, h694, hc23, hc34, hlam, hphi]
                                      · rcases h5bigk with h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [hlam, p696_0]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h472, hlam, p696_1]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [hc25, hlam, hphi, ht0b, ht5b, p696_1, u0elo4]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h675, hlam, p696_0]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h677, hlam, p696_1]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h681, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p696_1, u2elo1]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [hlam, p696_0]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h681, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p696_1, u2elo1]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h684, hlam, p696_0]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h686, hlam, p696_1]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h638, hlam, p696_1]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h681, hlam, p696_1]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [hlam, p696_0]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h690, hlam, p696_1]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h692, hlam, p696_1]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h471, h472, h679, h682, hc23, hc35, hlam, hphi, p696_1]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h471, h472, h679, h682, hc23, hc35, hlam, hphi, p696_1]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h690, hc23, hc35, hlam, hphi, p696_1]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [hlam, p696_0]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h694, hlam, p696_1]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h471, h472, h679, h682, hc23, hc45, hlam, hphi, ht34, p696_1]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h471, h472, h679, h682, hc23, hc45, hlam, hphi, ht34, p696_1]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h690, hc23, hc45, hlam, hphi, ht34, p696_1]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [h675, hc03, hc45, hlam, hphi, ht34, p696_1]
                                        · have p696_0 := h696c.1
                                          have p696_1 := h696c.2.1
                                          have p696_2 := h696c.2.2.1
                                          have p696_3 := h696c.2.2.2
                                          linarith only [hlam, p696_0]
                        · linarith only [h0, h681, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h471, h680, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h471, h636, h679, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h725 | h725
              · rcases m.htr 0 3 5 (by decide) (by decide) with h726 | h726
                · linarith only [h636, h638, h726, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h728 | h728
                  · linarith only [h0, h471, h638, h728, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h730 | h730
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h731 | h731
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h732 | h732
                        · linarith only [h636, h638, h732, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h471, h731, h732, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h0, h731, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h471, h636, h730, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h737 | h737
                · linarith only [h471, h472, h725, h737, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h739 | h739
                  · linarith only [h0, h471, h638, h739, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h741 | h741
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h742 | h742
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h743 | h743
                        · linarith only [h0, h638, h743, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h471, h742, h743, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h0, h471, h742, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h471, h741, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h0, h471, h637, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h749 | h749
          · rcases m.htr 0 2 5 (by decide) (by decide) with h750 | h750
            · rcases m.htr 0 3 4 (by decide) (by decide) with h751 | h751
              · rcases m.htr 0 3 5 (by decide) (by decide) with h752 | h752
                · rcases m.htr 0 4 5 (by decide) (by decide) with h753 | h753
                  · linarith only [h471, h472, h753, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h755 | h755
                    · linarith only [h472, h636, h750, h755, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h471, h755, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h636, h750, h752, hlam]
              · linarith only [h471, h472, h636, h750, h751, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h760 | h760
              · rcases m.htr 0 3 5 (by decide) (by decide) with h761 | h761
                · rcases m.htr 0 4 5 (by decide) (by decide) with h762 | h762
                  · linarith only [h0, h471, h750, h762, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h764 | h764
                    · linarith only [h0, h471, h636, h764, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h471, h764, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h767 | h767
                  · linarith only [h471, h472, h767, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h769 | h769
                    · linarith only [h0, h471, h636, h769, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h471, h769, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h0, h471, h636, h760, hlam]
          · linarith only [h0, h471, h749, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h774 | h774
      · rcases m.htr 0 2 3 (by decide) (by decide) with h775 | h775
        · rcases m.htr 0 2 4 (by decide) (by decide) with h776 | h776
          · rcases m.htr 0 2 5 (by decide) (by decide) with h777 | h777
            · rcases m.htr 0 3 4 (by decide) (by decide) with h778 | h778
              · rcases m.htr 0 3 5 (by decide) (by decide) with h779 | h779
                · rcases m.htr 0 4 5 (by decide) (by decide) with h780 | h780
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h781 | h781
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h782 | h782
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h783 | h783
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h784 | h784
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h785 | h785
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h786 | h786
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h787 | h787
                                · linarith only [h775, h787, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h778, h787, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h471, h780, h786, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                            · linarith only [h471, h774, h775, h779, h783, h784, h785, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h775, h778, h784, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h471, h782, h783, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h774, h776, h782, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h0, h774, h781, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h471, h774, h780, hlam]
                · linarith only [h471, h774, h778, h779, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h798 | h798
                · rcases m.htr 0 4 5 (by decide) (by decide) with h799 | h799
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h800 | h800
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h801 | h801
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h802 | h802
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h803 | h803
                          · linarith only [h778, h798, h800, h803, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h805 | h805
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h806 | h806
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h807 | h807
                                · linarith only [h471, h775, h803, h807, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h809 | h809
                                  · linarith only [h776, h807, h809, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h798, h809, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h471, h774, h776, h799, h802, h806, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h798, h805, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h802, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h774, h776, h801, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h0, h774, h800, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h471, h774, h799, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h818 | h818
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h819 | h819
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h820 | h820
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h821 | h821
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h822 | h822
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h823 | h823
                            · linarith only [h0, h774, h775, h798, h823, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h775, h778, h822, h823, hc23, hc35, hlam, hphi]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h826 | h826
                            · linarith only [h775, h798, h822, h826, hc23, hc34, hlam, hphi]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h828 | h828
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h829 | h829
                                · linarith only [h774, h819, h826, h829, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h831 | h831
                                  · linarith only [h775, h798, h831, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h833 | h833
                                    · linarith only [h776, h833, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h776, h818, h833, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h471, h818, h828, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                        · linarith only [h471, h774, h820, h821, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                      · linarith only [h0, h774, h820, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h0, h774, h775, h819, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h471, h774, h818, hlam]
            · linarith only [h0, h774, h777, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h842 | h842
            · rcases m.htr 0 3 4 (by decide) (by decide) with h843 | h843
              · linarith only [h775, h776, h843, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h845 | h845
                · rcases m.htr 0 4 5 (by decide) (by decide) with h846 | h846
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h847 | h847
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h848 | h848
                      · linarith only [h0, h776, h848, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h774, h848, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h0, h774, h775, h847, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h471, h774, h846, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h853 | h853
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h854 | h854
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h855 | h855
                      · linarith only [h776, h855, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h774, h855, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h0, h774, h775, h854, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h471, h774, h853, hlam]
            · linarith only [h0, h774, h842, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h861 | h861
          · rcases m.htr 0 2 5 (by decide) (by decide) with h862 | h862
            · rcases m.htr 0 3 4 (by decide) (by decide) with h863 | h863
              · rcases m.htr 0 3 5 (by decide) (by decide) with h864 | h864
                · rcases m.htr 0 4 5 (by decide) (by decide) with h865 | h865
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h866 | h866
                    · linarith only [h471, h775, h861, h866, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h774, h866, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h471, h774, h865, hlam]
                · linarith only [h471, h774, h775, h861, h864, hlam]
              · linarith only [h775, h861, h863, hlam]
            · linarith only [h471, h774, h861, h862, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h873 | h873
            · rcases m.htr 0 3 4 (by decide) (by decide) with h874 | h874
              · rcases m.htr 0 3 5 (by decide) (by decide) with h875 | h875
                · rcases m.htr 0 4 5 (by decide) (by decide) with h876 | h876
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h877 | h877
                    · linarith only [h775, h877, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h774, h877, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h0, h774, h861, h876, hlam]
                · linarith only [h0, h774, h861, h874, h875, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h882 | h882
                · rcases m.htr 0 4 5 (by decide) (by decide) with h883 | h883
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h884 | h884
                    · linarith only [h0, h774, h775, h884, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h774, h884, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h471, h774, h883, hlam]
                · linarith only [h0, h774, h775, h882, hlam]
            · linarith only [h0, h774, h873, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h890 | h890
        · rcases m.htr 0 2 4 (by decide) (by decide) with h891 | h891
          · rcases m.htr 0 2 5 (by decide) (by decide) with h892 | h892
            · rcases m.htr 0 3 4 (by decide) (by decide) with h893 | h893
              · rcases m.htr 0 3 5 (by decide) (by decide) with h894 | h894
                · rcases m.htr 0 4 5 (by decide) (by decide) with h895 | h895
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h896 | h896
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h897 | h897
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h898 | h898
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h899 | h899
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h900 | h900
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h901 | h901
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h902 | h902
                                · linarith only [h890, h902, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h893, h902, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h895, h901, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                            · linarith only [h471, h894, h899, h900, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                          · linarith only [h890, h893, h899, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h892, h898, hlam]
                      · linarith only [h0, h891, h897, hlam]
                    · linarith only [h0, h896, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h911 | h911
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h912 | h912
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h913 | h913
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h914 | h914
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h915 | h915
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h916 | h916
                              · linarith only [h471, h895, h911, h914, h916, hc01, hlam, hphi, ht12, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h918 | h918
                                · linarith only [h890, h918, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h890, h893, h918, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h890, h894, h915, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h890, h893, h911, h914, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h892, h913, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h891, h912, hlam]
                    · linarith only [h0, h911, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h926 | h926
                  · linarith only [h893, h894, h926, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h928 | h928
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h929 | h929
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h930 | h930
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h931 | h931
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h932 | h932
                            · linarith only [h471, h893, h894, h928, h932, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h934 | h934
                              · linarith only [h471, h926, h930, h931, h932, h934, hc01, hlam, hphi, ht12, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h936 | h936
                                · linarith only [h890, h936, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h893, h936, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h892, h893, h894, h931, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h892, h930, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h891, h929, hlam]
                    · linarith only [h0, h928, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h943 | h943
                · rcases m.htr 0 4 5 (by decide) (by decide) with h944 | h944
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h945 | h945
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h946 | h946
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h947 | h947
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h948 | h948
                          · linarith only [h893, h943, h945, h948, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h950 | h950
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h951 | h951
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h952 | h952
                                · linarith only [h890, h952, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h954 | h954
                                  · linarith only [h891, h952, h954, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h943, h954, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h774, h891, h944, h948, h950, h951, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h891, h893, h943, h950, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h892, h947, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h891, h946, hlam]
                    · linarith only [h0, h945, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h893, h943, h944, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h963 | h963
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h964 | h964
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h965 | h965
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h966 | h966
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h967 | h967
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h968 | h968
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h969 | h969
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h970 | h970
                                · linarith only [h890, h893, h970, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h972 | h972
                                  · linarith only [h890, h943, h972, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h974 | h974
                                    · linarith only [h891, h974, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h963, h974, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                              · linarith only [h893, h963, h964, h967, h969, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h893, h967, h968, hc03, hc35, hlam, hphi]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h979 | h979
                            · linarith only [h890, h943, h967, h979, hc23, hc34, hlam, hphi]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h981 | h981
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h982 | h982
                                · linarith only [h890, h967, h982, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h984 | h984
                                  · linarith only [h774, h890, h979, h984, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h986 | h986
                                    · linarith only [h891, h986, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h891, h963, h982, h986, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · linarith only [h891, h963, h981, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h892, h966, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h965, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h964, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h993 | h993
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h994 | h994
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h995 | h995
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h996 | h996
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h997 | h997
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h998 | h998
                              · linarith only [h471, h963, h994, h998, hc01, hlam, hphi, ht12, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1000 | h1000
                                · linarith only [h1000, h890, h893, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1002 | h1002
                                  · linarith only [h1002, h890, h943, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1004 | h1004
                                    · linarith only [h1004, h891, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1006 | h1006
                                      · linarith only [h1006, h471, h993, h996, h998, hc01, hlam, hphi, ht12, u2elo1]
                                      · rcases h5bigk with h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [hlam, p1008_0]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h774, hlam, p1008_1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h1000, h1004, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1008_1, u0elo4]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h943, hlam, p1008_0]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h963, hlam, p1008_1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h774, hc01, hc15, hlam, hphi, p1008_1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [hlam, p1008_0]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h1000, h1004, h995, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1008_1, u2elo1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h1006, h893, h993, h997, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1008_1, u2elo1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h998, hlam, p1008_1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h892, hlam, p1008_1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h995, hlam, p1008_1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [hlam, p1008_0]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h1002, hlam, p1008_1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h1004, hlam, p1008_1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h471, h963, hc01, hc35, hlam, hphi, ht12, ht23, p1008_1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h997, hlam, p1008_1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h1000, h1004, h993, h997, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1008_1, u2elo1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [hlam, p1008_0]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h1006, hlam, p1008_1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h471, h963, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1008_1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h774, h890, h893, h993, h996, hc01, hc23, hc45, hlam, hphi, ht12, ht34, p1008_1, u2elo1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h1000, h1004, hc23, hc45, hlam, hphi, ht34, p1008_1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [h890, h943, hc23, hc45, hlam, hphi, ht34, p1008_1]
                                        · have p1008_0 := h1008c.1
                                          have p1008_1 := h1008c.2.1
                                          have p1008_2 := h1008c.2.2.1
                                          have p1008_3 := h1008c.2.2.2
                                          linarith only [hlam, p1008_0]
                            · linarith only [h890, h893, h996, h997, hc23, hc35, hlam, hphi]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1035 | h1035
                            · linarith only [h1035, h890, h943, h996, hc23, hc34, hlam, hphi]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1037 | h1037
                              · linarith only [h1037, h471, h963, h994, hc01, hlam, hphi, ht12, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1039 | h1039
                                · linarith only [h1039, h890, h996, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1041 | h1041
                                  · linarith only [h1035, h1037, h1041, h471, h890, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1043 | h1043
                                    · linarith only [h1043, h891, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1045 | h1045
                                      · linarith only [h1037, h1045, h471, hc01, hc34, hlam, hphi, ht12, ht23]
                                      · rcases h5bigk with h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c | h1047c
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [hlam, p1047_0]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h774, hlam, p1047_1]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h1039, h1043, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1047_1, u0elo4]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h943, hlam, p1047_0]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h963, hlam, p1047_1]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h995, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1047_1, u2elo1]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [hlam, p1047_0]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h1039, h1043, h995, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1047_1, u2elo1]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h1035, hlam, p1047_0]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h1037, hlam, p1047_1]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h892, hlam, p1047_1]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h995, hlam, p1047_1]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [hlam, p1047_0]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h1041, hlam, p1047_1]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h1043, hlam, p1047_1]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h471, h963, hc01, hc35, hlam, hphi, ht12, ht23, p1047_1]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h774, hc01, hc35, hlam, hphi, ht12, ht23, p1047_1]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h1039, h1043, hc23, hc35, hlam, hphi, p1047_1]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [hlam, p1047_0]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h1045, hlam, p1047_1]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h471, h963, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1047_1]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h1037, h471, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1047_1]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h1039, h1043, hc23, hc45, hlam, hphi, ht34, p1047_1]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [h943, hc03, hc45, hlam, hphi, ht34, p1047_1]
                                        · have p1047_0 := h1047c.1
                                          have p1047_1 := h1047c.2.1
                                          have p1047_2 := h1047c.2.2.1
                                          have p1047_3 := h1047c.2.2.2
                                          linarith only [hlam, p1047_0]
                        · linarith only [h892, h995, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h994, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h890, h891, h993, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1076 | h1076
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1077 | h1077
                · linarith only [h1077, h890, h892, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1079 | h1079
                  · linarith only [h1079, h891, h892, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1081 | h1081
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1082 | h1082
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1083 | h1083
                        · linarith only [h1083, h892, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h1083, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h1082, h891, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1081, h890, h892, hc01, hlam, hphi, ht12, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1088 | h1088
                · linarith only [h1076, h1088, h891, h892, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1090 | h1090
                  · linarith only [h1090, h891, h892, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1092 | h1092
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1093 | h1093
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1094 | h1094
                        · linarith only [h1094, h892, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h1094, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h1093, h891, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1092, h890, h892, hc01, hlam, hphi, ht12, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1099 | h1099
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1100 | h1100
              · linarith only [h1100, h890, h891, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1102 | h1102
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1103 | h1103
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1104 | h1104
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1105 | h1105
                      · linarith only [h1105, h891, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1105, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1104, h890, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1102, h1103, h890, h891, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1110 | h1110
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1111 | h1111
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1112 | h1112
                      · linarith only [h1112, h891, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1112, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1111, h890, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1099, h1110, h891, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1117 | h1117
              · linarith only [h1117, h890, h891, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1119 | h1119
                · linarith only [h1099, h1119, h890, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1121 | h1121
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1122 | h1122
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1123 | h1123
                      · linarith only [h1123, h891, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1123, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1122, h890, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1127 | h1127
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1128 | h1128
                      · linarith only [h1128, h891, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1128, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1127, h890, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1132 | h1132
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1133 | h1133
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1134 | h1134
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1135 | h1135
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1136 | h1136
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1137 | h1137
                    · linarith only [h1137, h890, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1137, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1140 | h1140
                    · linarith only [h1132, h1140, h890, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1140, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1133, h1135, h890, hlam]
              · linarith only [h1132, h1134, h890, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1145 | h1145
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1146 | h1146
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1147 | h1147
                  · linarith only [h1132, h1133, h1147, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1149 | h1149
                    · linarith only [h1132, h1149, h890, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1149, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1152 | h1152
                  · linarith only [h1132, h1146, h1152, h890, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1154 | h1154
                    · linarith only [h1132, h1154, h890, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1154, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1132, h1145, h890, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1158 | h1158
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1159 | h1159
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1160 | h1160
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1161 | h1161
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1162 | h1162
                    · linarith only [h1158, h1162, h890, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h1162, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h1132, h1158, h1161, hlam]
                · linarith only [h1132, h1158, h1159, h1160, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1167 | h1167
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1168 | h1168
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1169 | h1169
                    · linarith only [h1158, h1169, h890, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h1169, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h1158, h1159, h1168, h890, hlam]
                · linarith only [h1158, h1167, h890, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1174 | h1174
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1175 | h1175
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1176 | h1176
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1177 | h1177
                    · linarith only [h1177, h890, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1177, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1180 | h1180
                    · linarith only [h0, h1180, h890, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1180, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1183 | h1183
                  · linarith only [h1174, h1175, h1183, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1185 | h1185
                    · linarith only [h0, h1185, h890, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1185, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1188 | h1188
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1189 | h1189
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1190 | h1190
                    · linarith only [h0, h1190, h890, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1190, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h1174, h1188, h1189, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1194 | h1194
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1195 | h1195
                    · linarith only [h0, h1195, h890, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1195, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1198 | h1198
                    · linarith only [h0, h1198, h890, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1198, hc01, hlam, hphi, ht12, u2elo2]

theorem n7l_sBT2_M_LI_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h6 | h6
    · linarith only [h6, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h8 | h8
      · rcases p0_3 (m.d 2 5) (by simp) with h9 | h9
        · rcases p0_3 (m.d 3 5) (by simp) with h10 | h10
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · rcases m.htr 0 1 3 (by decide) (by decide) with h12 | h12
              · rcases m.htr 0 1 5 (by decide) (by decide) with h13 | h13
                · linarith only [h13, hlam, p0_0]
                · linarith only [h11, h13, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h16 | h16
                · linarith only [h16, hlam, p0_0]
                · linarith only [h11, h16, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h19 | h19
              · rcases m.htr 0 1 5 (by decide) (by decide) with h20 | h20
                · linarith only [h20, hlam, p0_0]
                · linarith only [h19, h20, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h23 | h23
                · linarith only [h23, hlam, p0_0]
                · linarith only [h10, h23, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · rcases m.htr 0 1 3 (by decide) (by decide) with h27 | h27
              · rcases m.htr 0 1 5 (by decide) (by decide) with h28 | h28
                · linarith only [h28, hlam, p0_0]
                · linarith only [h26, h28, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h31 | h31
                · linarith only [h31, hlam, p0_0]
                · linarith only [h26, h31, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h34 | h34
              · rcases m.htr 0 1 5 (by decide) (by decide) with h35 | h35
                · linarith only [h35, hlam, p0_0]
                · linarith only [h34, h35, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h38 | h38
                · linarith only [h38, hlam, p0_0]
                · linarith only [h38, h9, hc01, hc25, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h41 | h41
          · rcases p0_3 (m.d 4 5) (by simp) with h42 | h42
            · rcases m.htr 0 1 3 (by decide) (by decide) with h43 | h43
              · rcases m.htr 0 1 5 (by decide) (by decide) with h44 | h44
                · linarith only [h44, hlam, p0_0]
                · linarith only [h42, h44, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h47 | h47
                · linarith only [h47, hlam, p0_0]
                · linarith only [h42, h47, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h50 | h50
              · rcases m.htr 0 1 5 (by decide) (by decide) with h51 | h51
                · linarith only [h51, hlam, p0_0]
                · linarith only [h50, h51, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h54 | h54
                · linarith only [h54, hlam, p0_0]
                · linarith only [h41, h54, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h57 | h57
            · rcases m.htr 0 1 3 (by decide) (by decide) with h58 | h58
              · rcases m.htr 0 1 5 (by decide) (by decide) with h59 | h59
                · linarith only [h59, hlam, p0_0]
                · linarith only [h57, h59, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h62 | h62
                · linarith only [h62, hlam, p0_0]
                · linarith only [h57, h62, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h65 | h65
              · rcases m.htr 0 1 5 (by decide) (by decide) with h66 | h66
                · linarith only [h66, hlam, p0_0]
                · linarith only [h65, h66, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h69 | h69
                · linarith only [h69, hlam, p0_0]
                · linarith only [h69, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h8, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h74 | h74
    · linarith only [h74, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h76 | h76
      · rcases p0_3 (m.d 2 5) (by simp) with h77 | h77
        · linarith only [h77, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h79 | h79
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · rcases m.htr 0 1 3 (by decide) (by decide) with h81 | h81
              · rcases m.htr 0 1 5 (by decide) (by decide) with h82 | h82
                · linarith only [h82, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h74, h81, h82, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h85 | h85
                · linarith only [h74, h81, h85, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                · linarith only [h74, h80, h85, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h88 | h88
              · rcases m.htr 0 1 5 (by decide) (by decide) with h89 | h89
                · linarith only [h74, h89, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h74, h89, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h92 | h92
                · linarith only [h74, h88, h92, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                · linarith only [h74, h79, h92, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h95 | h95
            · rcases m.htr 0 1 3 (by decide) (by decide) with h96 | h96
              · rcases m.htr 0 1 5 (by decide) (by decide) with h97 | h97
                · linarith only [h74, h97, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h74, h96, h97, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h100 | h100
                · linarith only [h100, h74, h96, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                · linarith only [h100, h74, h95, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h103 | h103
              · rcases m.htr 0 1 5 (by decide) (by decide) with h104 | h104
                · linarith only [h104, h74, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h104, h74, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h107 | h107
                · linarith only [h103, h107, h74, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                · linarith only [h107, h74, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h76, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h111 | h111
    · linarith only [h111, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h113 | h113
      · rcases p0_3 (m.d 2 5) (by simp) with h114 | h114
        · rcases p0_3 (m.d 3 5) (by simp) with h115 | h115
          · linarith only [h115, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h117 | h117
            · rcases m.htr 0 1 3 (by decide) (by decide) with h118 | h118
              · rcases m.htr 0 1 5 (by decide) (by decide) with h119 | h119
                · linarith only [h119, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h111, h119, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h122 | h122
                · linarith only [h111, h118, h122, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                · linarith only [h111, h117, h122, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h125 | h125
              · rcases m.htr 0 1 5 (by decide) (by decide) with h126 | h126
                · linarith only [h111, h126, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h111, h114, h126, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h129 | h129
                · linarith only [h111, h125, h129, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                · linarith only [h111, h114, h129, hc01, hc25, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h134 | h134
            · rcases m.htr 0 1 3 (by decide) (by decide) with h135 | h135
              · rcases m.htr 0 1 5 (by decide) (by decide) with h136 | h136
                · linarith only [h111, h136, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h111, h134, h136, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h139 | h139
                · linarith only [h111, h135, h139, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                · linarith only [h111, h134, h139, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h142 | h142
              · rcases m.htr 0 1 5 (by decide) (by decide) with h143 | h143
                · linarith only [h111, h143, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h111, h143, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h146 | h146
                · linarith only [h111, h146, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h111, h146, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h113, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h150 | h150
    · linarith only [h150, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h152 | h152
      · rcases p0_3 (m.d 2 5) (by simp) with h153 | h153
        · rcases p0_3 (m.d 3 5) (by simp) with h154 | h154
          · rcases p0_3 (m.d 4 5) (by simp) with h155 | h155
            · linarith only [h155, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h157 | h157
              · rcases m.htr 0 1 5 (by decide) (by decide) with h158 | h158
                · linarith only [h158, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h150, h158, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h161 | h161
                · linarith only [h150, h161, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h150, h161, hc01, hc15, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h164 | h164
            · linarith only [h164, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h166 | h166
              · rcases m.htr 0 1 5 (by decide) (by decide) with h167 | h167
                · linarith only [h150, h167, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h150, h153, h166, h167, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h170 | h170
                · linarith only [h150, h166, h170, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                · linarith only [h150, h153, h170, hc01, hc25, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h173 | h173
          · rcases p0_3 (m.d 4 5) (by simp) with h174 | h174
            · linarith only [h174, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h176 | h176
              · rcases m.htr 0 1 5 (by decide) (by decide) with h177 | h177
                · linarith only [h150, h177, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h150, h173, h176, h177, hc13, hc35, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h180 | h180
                · linarith only [h150, h180, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h150, h173, h180, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h183 | h183
            · linarith only [h183, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h185 | h185
              · rcases m.htr 0 1 5 (by decide) (by decide) with h186 | h186
                · linarith only [h150, h186, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h150, h185, h186, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h189 | h189
                · linarith only [h150, h185, h189, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                · linarith only [h150, h189, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h152, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h193 | h193
    · linarith only [h193, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h195 | h195
      · rcases p0_3 (m.d 2 5) (by simp) with h196 | h196
        · rcases p0_3 (m.d 3 5) (by simp) with h197 | h197
          · rcases p0_3 (m.d 4 5) (by simp) with h198 | h198
            · rcases m.htr 0 1 3 (by decide) (by decide) with h199 | h199
              · rcases m.htr 0 1 5 (by decide) (by decide) with h200 | h200
                · linarith only [h195, h200, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h200, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h203 | h203
                · linarith only [h195, h203, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h203, hc01, hc25, hlam, hphi, ht12, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h206 | h206
              · rcases m.htr 0 1 5 (by decide) (by decide) with h207 | h207
                · linarith only [h195, h207, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h207, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h210 | h210
                · linarith only [h195, h210, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h210, hc01, hc25, hlam, hphi, ht12, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h213 | h213
            · rcases m.htr 0 1 3 (by decide) (by decide) with h214 | h214
              · rcases m.htr 0 1 5 (by decide) (by decide) with h215 | h215
                · linarith only [h195, h215, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h215, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h218 | h218
                · linarith only [h195, h218, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h218, hc01, hc25, hlam, hphi, ht12, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h221 | h221
              · rcases m.htr 0 1 5 (by decide) (by decide) with h222 | h222
                · linarith only [h195, h222, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h222, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h225 | h225
                · linarith only [h195, h221, h225, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                · linarith only [h225, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h196, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h229 | h229
        · rcases p0_3 (m.d 3 5) (by simp) with h230 | h230
          · rcases p0_3 (m.d 4 5) (by simp) with h231 | h231
            · rcases m.htr 0 1 3 (by decide) (by decide) with h232 | h232
              · rcases m.htr 0 1 5 (by decide) (by decide) with h233 | h233
                · rcases m.htr 0 2 4 (by decide) (by decide) with h234 | h234
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h235 | h235
                    · linarith only [h235, hlam, p0_0]
                    · linarith only [h231, h235, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h238 | h238
                    · linarith only [h238, hlam, p0_0]
                    · linarith only [h231, h238, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h195, h233, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h242 | h242
                · rcases m.htr 0 2 4 (by decide) (by decide) with h243 | h243
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h244 | h244
                    · linarith only [h244, hlam, p0_0]
                    · linarith only [h231, h244, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h247 | h247
                    · linarith only [h247, hlam, p0_0]
                    · linarith only [h231, h247, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h195, h242, hlam]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h251 | h251
              · rcases m.htr 0 1 5 (by decide) (by decide) with h252 | h252
                · rcases m.htr 0 2 4 (by decide) (by decide) with h253 | h253
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h254 | h254
                    · linarith only [h254, hlam, p0_0]
                    · linarith only [h253, h254, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h257 | h257
                    · linarith only [h257, hlam, p0_0]
                    · linarith only [h230, h257, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h195, h252, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h261 | h261
                · rcases m.htr 0 2 4 (by decide) (by decide) with h262 | h262
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h263 | h263
                    · linarith only [h263, hlam, p0_0]
                    · linarith only [h230, h263, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h266 | h266
                    · linarith only [h266, hlam, p0_0]
                    · linarith only [h230, h266, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h195, h261, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h270 | h270
            · rcases m.htr 0 1 3 (by decide) (by decide) with h271 | h271
              · rcases m.htr 0 1 5 (by decide) (by decide) with h272 | h272
                · rcases m.htr 0 2 4 (by decide) (by decide) with h273 | h273
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h274 | h274
                    · linarith only [h274, hlam, p0_0]
                    · linarith only [h270, h274, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h277 | h277
                    · linarith only [h277, hlam, p0_0]
                    · linarith only [h270, h277, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h195, h272, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h281 | h281
                · rcases m.htr 0 2 4 (by decide) (by decide) with h282 | h282
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h283 | h283
                    · linarith only [h283, hlam, p0_0]
                    · linarith only [h270, h282, h283, hc24, hc45, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h286 | h286
                    · linarith only [h286, hlam, p0_0]
                    · linarith only [h270, h286, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h195, h281, hlam]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h290 | h290
              · rcases m.htr 0 1 5 (by decide) (by decide) with h291 | h291
                · rcases m.htr 0 2 4 (by decide) (by decide) with h292 | h292
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h293 | h293
                    · linarith only [h293, hlam, p0_0]
                    · linarith only [h292, h293, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h296 | h296
                    · linarith only [h296, hlam, p0_0]
                    · linarith only [h296, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h195, h291, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h300 | h300
                · rcases m.htr 0 2 4 (by decide) (by decide) with h301 | h301
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h302 | h302
                    · linarith only [h302, hlam, p0_0]
                    · linarith only [h301, h302, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h305 | h305
                    · linarith only [h305, hlam, p0_0]
                    · linarith only [h305, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h195, h300, hlam]
        · linarith only [h229, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h310 | h310
    · linarith only [h310, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h312 | h312
      · linarith only [h312, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h314 | h314
        · rcases p0_3 (m.d 3 5) (by simp) with h315 | h315
          · rcases p0_3 (m.d 4 5) (by simp) with h316 | h316
            · rcases m.htr 0 1 3 (by decide) (by decide) with h317 | h317
              · rcases m.htr 0 1 5 (by decide) (by decide) with h318 | h318
                · linarith only [h310, h318, hlam]
                · linarith only [h316, h318, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h321 | h321
                · linarith only [h310, h321, hlam]
                · linarith only [h316, h321, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h324 | h324
              · rcases m.htr 0 1 5 (by decide) (by decide) with h325 | h325
                · linarith only [h310, h325, hlam]
                · linarith only [h315, h325, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h328 | h328
                · linarith only [h310, h328, hlam]
                · linarith only [h315, h328, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h331 | h331
            · rcases m.htr 0 1 3 (by decide) (by decide) with h332 | h332
              · rcases m.htr 0 1 5 (by decide) (by decide) with h333 | h333
                · linarith only [h310, h333, hlam]
                · linarith only [h331, h333, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h336 | h336
                · linarith only [h310, h336, hlam]
                · linarith only [h331, h336, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h339 | h339
              · rcases m.htr 0 1 5 (by decide) (by decide) with h340 | h340
                · linarith only [h310, h340, hlam]
                · linarith only [h339, h340, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h343 | h343
                · linarith only [h310, h343, hlam]
                · linarith only [h343, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h314, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h348 | h348
    · linarith only [h348, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h350 | h350
      · rcases p0_3 (m.d 2 5) (by simp) with h351 | h351
        · rcases p0_3 (m.d 3 5) (by simp) with h352 | h352
          · linarith only [h352, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h354 | h354
            · rcases m.htr 0 1 3 (by decide) (by decide) with h355 | h355
              · rcases m.htr 0 1 5 (by decide) (by decide) with h356 | h356
                · linarith only [h350, h356, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h348, h356, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h359 | h359
                · linarith only [h348, h350, h359, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h348, h359, hc01, hc25, hlam, hphi, ht12, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h362 | h362
              · rcases m.htr 0 1 5 (by decide) (by decide) with h363 | h363
                · linarith only [h348, h350, h363, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h348, h363, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h366 | h366
                · linarith only [h348, h350, h366, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h348, h366, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h351, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h370 | h370
        · rcases p0_3 (m.d 3 5) (by simp) with h371 | h371
          · linarith only [h371, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h373 | h373
            · rcases m.htr 0 1 3 (by decide) (by decide) with h374 | h374
              · rcases m.htr 0 1 5 (by decide) (by decide) with h375 | h375
                · rcases m.htr 0 2 4 (by decide) (by decide) with h376 | h376
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h377 | h377
                    · linarith only [h348, h375, h377, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h348, h373, h377, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h380 | h380
                    · linarith only [h348, h375, h380, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h348, h373, h380, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h350, h373, h374, h375, hc13, hc45, hlam, hphi, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h384 | h384
                · rcases m.htr 0 2 4 (by decide) (by decide) with h385 | h385
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h386 | h386
                    · linarith only [h348, h384, h386, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h348, h373, h386, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h389 | h389
                    · linarith only [h348, h384, h389, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h348, h373, h389, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h350, h373, h384, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h393 | h393
              · rcases m.htr 0 1 5 (by decide) (by decide) with h394 | h394
                · rcases m.htr 0 2 4 (by decide) (by decide) with h395 | h395
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h396 | h396
                    · linarith only [h348, h396, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h348, h396, hc02, hc25, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h399 | h399
                    · linarith only [h348, h395, h399, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                    · linarith only [h348, h399, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h350, h393, h394, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h403 | h403
                · rcases m.htr 0 2 4 (by decide) (by decide) with h404 | h404
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h405 | h405
                    · linarith only [h348, h405, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h348, h405, hc02, hc25, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h408 | h408
                    · linarith only [h348, h404, h408, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                    · linarith only [h348, h408, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h350, h403, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h370, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h413 | h413
    · linarith only [h413, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h415 | h415
      · rcases p0_3 (m.d 2 5) (by simp) with h416 | h416
        · rcases p0_3 (m.d 3 5) (by simp) with h417 | h417
          · rcases p0_3 (m.d 4 5) (by simp) with h418 | h418
            · linarith only [h418, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h420 | h420
              · rcases m.htr 0 1 5 (by decide) (by decide) with h421 | h421
                · linarith only [h415, h421, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h413, h421, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h424 | h424
                · linarith only [h413, h415, h424, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h413, h424, hc01, hc25, hlam, hphi, ht12, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h427 | h427
            · linarith only [h427, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h429 | h429
              · rcases m.htr 0 1 5 (by decide) (by decide) with h430 | h430
                · linarith only [h413, h415, h430, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h413, h430, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h433 | h433
                · linarith only [h413, h415, h433, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h413, h433, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h416, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h437 | h437
        · rcases p0_3 (m.d 3 5) (by simp) with h438 | h438
          · rcases p0_3 (m.d 4 5) (by simp) with h439 | h439
            · linarith only [h439, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h441 | h441
              · rcases m.htr 0 1 5 (by decide) (by decide) with h442 | h442
                · rcases m.htr 0 2 4 (by decide) (by decide) with h443 | h443
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h444 | h444
                    · linarith only [h413, h444, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h413, h438, h443, h444, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h447 | h447
                    · linarith only [h413, h443, h447, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                    · linarith only [h413, h447, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h415, h438, h441, h442, hc13, hc35, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h451 | h451
                · rcases m.htr 0 2 4 (by decide) (by decide) with h452 | h452
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h453 | h453
                    · linarith only [h413, h453, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h413, h438, h452, h453, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h456 | h456
                    · linarith only [h413, h452, h456, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                    · linarith only [h413, h438, h456, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h415, h438, h451, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h460 | h460
            · linarith only [h460, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h462 | h462
              · rcases m.htr 0 1 5 (by decide) (by decide) with h463 | h463
                · rcases m.htr 0 2 4 (by decide) (by decide) with h464 | h464
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h465 | h465
                    · linarith only [h413, h465, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h413, h465, hc02, hc25, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h468 | h468
                    · linarith only [h413, h464, h468, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                    · linarith only [h413, h468, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h415, h462, h463, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h472 | h472
                · rcases m.htr 0 2 4 (by decide) (by decide) with h473 | h473
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h474 | h474
                    · linarith only [h413, h474, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h413, h473, h474, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h477 | h477
                    · linarith only [h413, h477, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h413, h477, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h415, h472, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h437, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h482 | h482
    · linarith only [h482, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h484 | h484
      · rcases p0_3 (m.d 2 5) (by simp) with h485 | h485
        · rcases p0_3 (m.d 3 5) (by simp) with h486 | h486
          · rcases p0_3 (m.d 4 5) (by simp) with h487 | h487
            · rcases m.htr 0 1 3 (by decide) (by decide) with h488 | h488
              · rcases m.htr 0 1 5 (by decide) (by decide) with h489 | h489
                · linarith only [h484, h489, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h489, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h492 | h492
                · linarith only [h484, h492, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h492, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h495 | h495
              · rcases m.htr 0 1 5 (by decide) (by decide) with h496 | h496
                · linarith only [h484, h496, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h496, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h499 | h499
                · linarith only [h484, h499, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h499, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h486, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h503 | h503
          · rcases p0_3 (m.d 4 5) (by simp) with h504 | h504
            · rcases m.htr 0 1 3 (by decide) (by decide) with h505 | h505
              · rcases m.htr 0 1 5 (by decide) (by decide) with h506 | h506
                · linarith only [h484, h506, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h506, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h509 | h509
                · linarith only [h484, h509, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h509, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h512 | h512
              · rcases m.htr 0 1 5 (by decide) (by decide) with h513 | h513
                · linarith only [h484, h513, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h513, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h516 | h516
                · linarith only [h484, h516, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h516, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h503, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h520 | h520
        · rcases p0_3 (m.d 3 5) (by simp) with h521 | h521
          · rcases p0_3 (m.d 4 5) (by simp) with h522 | h522
            · rcases m.htr 0 1 3 (by decide) (by decide) with h523 | h523
              · rcases m.htr 0 1 5 (by decide) (by decide) with h524 | h524
                · rcases m.htr 0 2 4 (by decide) (by decide) with h525 | h525
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h526 | h526
                    · linarith only [h520, h526, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h526, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h529 | h529
                    · linarith only [h520, h529, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h529, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h484, h524, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h533 | h533
                · rcases m.htr 0 2 4 (by decide) (by decide) with h534 | h534
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h535 | h535
                    · linarith only [h520, h535, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h535, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h538 | h538
                    · linarith only [h520, h538, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h538, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h484, h533, hlam]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h542 | h542
              · rcases m.htr 0 1 5 (by decide) (by decide) with h543 | h543
                · rcases m.htr 0 2 4 (by decide) (by decide) with h544 | h544
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h545 | h545
                    · linarith only [h520, h545, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h544, h545, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h548 | h548
                    · linarith only [h520, h548, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h548, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h484, h543, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h552 | h552
                · rcases m.htr 0 2 4 (by decide) (by decide) with h553 | h553
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h554 | h554
                    · linarith only [h520, h554, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h554, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h557 | h557
                    · linarith only [h520, h557, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h557, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h484, h552, hlam]
          · linarith only [h521, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h562 | h562
          · rcases p0_3 (m.d 4 5) (by simp) with h563 | h563
            · rcases m.htr 0 1 3 (by decide) (by decide) with h564 | h564
              · rcases m.htr 0 1 5 (by decide) (by decide) with h565 | h565
                · rcases m.htr 0 2 4 (by decide) (by decide) with h566 | h566
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h567 | h567
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h568 | h568
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h569 | h569
                        · linarith only [h569, hlam, p0_0]
                        · linarith only [h563, h569, hc03, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h572 | h572
                        · linarith only [h572, hlam, p0_0]
                        · linarith only [h563, h564, h572, hc13, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h520, h567, hlam]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h576 | h576
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h577 | h577
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h578 | h578
                        · linarith only [h578, hlam, p0_0]
                        · linarith only [h563, h577, h578, hc34, hc45, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h581 | h581
                        · linarith only [h581, hlam, p0_0]
                        · linarith only [h563, h581, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h520, h576, hlam]
                · linarith only [h484, h565, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h586 | h586
                · rcases m.htr 0 2 4 (by decide) (by decide) with h587 | h587
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h588 | h588
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h589 | h589
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h590 | h590
                        · linarith only [h590, hlam, p0_0]
                        · linarith only [h563, h589, h590, hc34, hc45, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h593 | h593
                        · linarith only [h593, hlam, p0_0]
                        · linarith only [h563, h593, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h520, h588, hlam]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h597 | h597
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h598 | h598
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h599 | h599
                        · linarith only [h599, hlam, p0_0]
                        · linarith only [h563, h598, h599, hc34, hc45, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h602 | h602
                        · linarith only [h602, hlam, p0_0]
                        · linarith only [h563, h602, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h520, h597, hlam]
                · linarith only [h484, h586, hlam]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h607 | h607
              · rcases m.htr 0 1 5 (by decide) (by decide) with h608 | h608
                · rcases m.htr 0 2 4 (by decide) (by decide) with h609 | h609
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h610 | h610
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h611 | h611
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h612 | h612
                        · linarith only [h612, hlam, p0_0]
                        · linarith only [h607, h612, hc13, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h615 | h615
                        · linarith only [h615, hlam, p0_0]
                        · linarith only [h607, h615, hc13, hc35, hlam, hphi, p0_1]
                    · linarith only [h520, h610, hlam]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h619 | h619
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h620 | h620
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h621 | h621
                        · linarith only [h621, hlam, p0_0]
                        · linarith only [h609, h620, h621, hc02, hc35, hlam, hphi, ht23, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h624 | h624
                        · linarith only [h624, hlam, p0_0]
                        · linarith only [h607, h624, hc13, hc35, hlam, hphi, p0_1]
                    · linarith only [h520, h619, hlam]
                · linarith only [h484, h608, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h629 | h629
                · rcases m.htr 0 2 4 (by decide) (by decide) with h630 | h630
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h631 | h631
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h632 | h632
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h633 | h633
                        · linarith only [h633, hlam, p0_0]
                        · linarith only [h607, h629, h633, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h636 | h636
                        · linarith only [h636, hlam, p0_0]
                        · linarith only [h607, h629, h636, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1]
                    · linarith only [h520, h631, hlam]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h640 | h640
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h641 | h641
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h642 | h642
                        · linarith only [h642, hlam, p0_0]
                        · linarith only [h630, h640, h641, h642, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h645 | h645
                        · linarith only [h645, hlam, p0_0]
                        · linarith only [h645, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h520, h640, hlam]
                · linarith only [h484, h629, hlam]
          · linarith only [h562, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h651 | h651
    · linarith only [h651, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h653 | h653
      · linarith only [h653, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h655 | h655
        · rcases p0_3 (m.d 3 5) (by simp) with h656 | h656
          · rcases p0_3 (m.d 4 5) (by simp) with h657 | h657
            · rcases m.htr 0 1 3 (by decide) (by decide) with h658 | h658
              · rcases m.htr 0 1 5 (by decide) (by decide) with h659 | h659
                · linarith only [h651, h659, hlam]
                · linarith only [h657, h658, h659, hc13, hc45, hlam, hphi, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h662 | h662
                · linarith only [h651, h662, hlam]
                · linarith only [h657, h662, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h665 | h665
              · rcases m.htr 0 1 5 (by decide) (by decide) with h666 | h666
                · linarith only [h651, h666, hlam]
                · linarith only [h655, h665, h666, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h669 | h669
                · linarith only [h651, h669, hlam]
                · linarith only [h669, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h656, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h673 | h673
          · rcases p0_3 (m.d 4 5) (by simp) with h674 | h674
            · rcases m.htr 0 1 3 (by decide) (by decide) with h675 | h675
              · rcases m.htr 0 1 5 (by decide) (by decide) with h676 | h676
                · linarith only [h651, h676, hlam]
                · linarith only [h674, h676, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h679 | h679
                · linarith only [h651, h679, hlam]
                · linarith only [h674, h679, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h682 | h682
              · rcases m.htr 0 1 5 (by decide) (by decide) with h683 | h683
                · linarith only [h651, h683, hlam]
                · linarith only [h682, h683, hc13, hc35, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h686 | h686
                · linarith only [h651, h686, hlam]
                · linarith only [h686, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h673, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h690 | h690
    · linarith only [h690, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h692 | h692
      · rcases p0_3 (m.d 2 5) (by simp) with h693 | h693
        · linarith only [h693, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h695 | h695
          · rcases p0_3 (m.d 4 5) (by simp) with h696 | h696
            · rcases m.htr 0 1 3 (by decide) (by decide) with h697 | h697
              · rcases m.htr 0 1 5 (by decide) (by decide) with h698 | h698
                · linarith only [h692, h698, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h690, h698, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h701 | h701
                · linarith only [h690, h692, h701, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h690, h701, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h704 | h704
              · rcases m.htr 0 1 5 (by decide) (by decide) with h705 | h705
                · linarith only [h690, h692, h705, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h690, h705, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h708 | h708
                · linarith only [h690, h692, h708, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h690, h708, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h695, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h712 | h712
        · linarith only [h712, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h714 | h714
          · rcases p0_3 (m.d 4 5) (by simp) with h715 | h715
            · rcases m.htr 0 1 3 (by decide) (by decide) with h716 | h716
              · rcases m.htr 0 1 5 (by decide) (by decide) with h717 | h717
                · rcases m.htr 0 2 4 (by decide) (by decide) with h718 | h718
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h719 | h719
                    · linarith only [h690, h719, hlam]
                    · linarith only [h715, h719, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h722 | h722
                    · linarith only [h690, h722, hlam]
                    · linarith only [h715, h722, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h692, h715, h716, h717, hc13, hc45, hlam, hphi, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h726 | h726
                · rcases m.htr 0 2 4 (by decide) (by decide) with h727 | h727
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h728 | h728
                    · linarith only [h690, h728, hlam]
                    · linarith only [h715, h728, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h731 | h731
                    · linarith only [h690, h731, hlam]
                    · linarith only [h715, h731, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h692, h715, h726, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h735 | h735
              · rcases m.htr 0 1 5 (by decide) (by decide) with h736 | h736
                · rcases m.htr 0 2 4 (by decide) (by decide) with h737 | h737
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h738 | h738
                    · linarith only [h690, h738, hlam]
                    · linarith only [h737, h738, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h741 | h741
                    · linarith only [h690, h741, hlam]
                    · linarith only [h741, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h692, h735, h736, hc13, hc35, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h745 | h745
                · rcases m.htr 0 2 4 (by decide) (by decide) with h746 | h746
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h747 | h747
                    · linarith only [h690, h747, hlam]
                    · linarith only [h746, h747, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h750 | h750
                    · linarith only [h690, h750, hlam]
                    · linarith only [h750, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h692, h745, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h714, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h756 | h756
    · linarith only [h756, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h758 | h758
      · rcases p0_3 (m.d 2 5) (by simp) with h759 | h759
        · rcases p0_3 (m.d 3 5) (by simp) with h760 | h760
          · rcases p0_3 (m.d 4 5) (by simp) with h761 | h761
            · linarith only [h761, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h763 | h763
              · rcases m.htr 0 1 5 (by decide) (by decide) with h764 | h764
                · linarith only [h758, h764, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h756, h759, h764, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h767 | h767
                · linarith only [h756, h758, h767, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h756, h767, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h760, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h771 | h771
          · rcases p0_3 (m.d 4 5) (by simp) with h772 | h772
            · linarith only [h772, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h774 | h774
              · rcases m.htr 0 1 5 (by decide) (by decide) with h775 | h775
                · linarith only [h756, h758, h775, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h756, h775, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h778 | h778
                · linarith only [h756, h758, h774, h778, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                · linarith only [h756, h778, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h771, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h782 | h782
        · rcases p0_3 (m.d 3 5) (by simp) with h783 | h783
          · rcases p0_3 (m.d 4 5) (by simp) with h784 | h784
            · linarith only [h784, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h786 | h786
              · rcases m.htr 0 1 5 (by decide) (by decide) with h787 | h787
                · rcases m.htr 0 2 4 (by decide) (by decide) with h788 | h788
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h789 | h789
                    · linarith only [h756, h782, h789, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h756, h788, h789, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h792 | h792
                    · linarith only [h756, h782, h788, h792, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                    · linarith only [h756, h792, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h758, h786, h787, hc13, hc35, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h796 | h796
                · rcases m.htr 0 2 4 (by decide) (by decide) with h797 | h797
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h798 | h798
                    · linarith only [h756, h782, h798, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h756, h798, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h801 | h801
                    · linarith only [h756, h782, h797, h801, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                    · linarith only [h756, h801, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h758, h796, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h783, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h806 | h806
          · rcases p0_3 (m.d 4 5) (by simp) with h807 | h807
            · linarith only [h807, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h809 | h809
              · rcases m.htr 0 1 5 (by decide) (by decide) with h810 | h810
                · rcases m.htr 0 2 4 (by decide) (by decide) with h811 | h811
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h812 | h812
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h813 | h813
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h814 | h814
                        · linarith only [h756, h809, h814, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                        · linarith only [h756, h814, hc03, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h817 | h817
                        · linarith only [h756, h817, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h756, h817, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h782, h812, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h821 | h821
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h822 | h822
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h823 | h823
                        · linarith only [h756, h823, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h756, h823, hc03, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h826 | h826
                        · linarith only [h756, h826, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h756, h826, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h782, h821, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h758, h810, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h831 | h831
                · rcases m.htr 0 2 4 (by decide) (by decide) with h832 | h832
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h833 | h833
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h834 | h834
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h835 | h835
                        · linarith only [h756, h835, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h756, h835, hc03, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h838 | h838
                        · linarith only [h756, h832, h834, h838, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                        · linarith only [h756, h838, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h782, h833, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h842 | h842
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h843 | h843
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h844 | h844
                        · linarith only [h756, h844, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h756, h844, hc03, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h847 | h847
                        · linarith only [h756, h843, h847, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                        · linarith only [h756, h847, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h782, h842, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h758, h831, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h806, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h853 | h853
    · linarith only [h853, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h855 | h855
      · rcases p0_3 (m.d 2 5) (by simp) with h856 | h856
        · rcases p0_3 (m.d 3 5) (by simp) with h857 | h857
          · rcases p0_3 (m.d 4 5) (by simp) with h858 | h858
            · rcases m.htr 0 1 3 (by decide) (by decide) with h859 | h859
              · rcases m.htr 0 1 5 (by decide) (by decide) with h860 | h860
                · linarith only [h855, h860, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h856, h860, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h863 | h863
                · linarith only [h855, h863, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h863, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h858, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h867 | h867
            · rcases m.htr 0 1 3 (by decide) (by decide) with h868 | h868
              · rcases m.htr 0 1 5 (by decide) (by decide) with h869 | h869
                · linarith only [h855, h869, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h869, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h872 | h872
                · linarith only [h855, h872, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h872, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h867, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h876 | h876
          · rcases p0_3 (m.d 4 5) (by simp) with h877 | h877
            · rcases m.htr 0 1 3 (by decide) (by decide) with h878 | h878
              · rcases m.htr 0 1 5 (by decide) (by decide) with h879 | h879
                · linarith only [h855, h879, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h876, h879, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h882 | h882
                · linarith only [h855, h882, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h882, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h877, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h886 | h886
            · rcases m.htr 0 1 3 (by decide) (by decide) with h887 | h887
              · rcases m.htr 0 1 5 (by decide) (by decide) with h888 | h888
                · linarith only [h855, h888, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h888, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h891 | h891
                · linarith only [h855, h891, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h891, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h886, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h895 | h895
        · rcases p0_3 (m.d 3 5) (by simp) with h896 | h896
          · rcases p0_3 (m.d 4 5) (by simp) with h897 | h897
            · rcases m.htr 0 1 3 (by decide) (by decide) with h898 | h898
              · rcases m.htr 0 1 5 (by decide) (by decide) with h899 | h899
                · rcases m.htr 0 2 4 (by decide) (by decide) with h900 | h900
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h901 | h901
                    · linarith only [h895, h899, h901, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h901, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h904 | h904
                    · linarith only [h895, h899, h904, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h904, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h855, h899, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h908 | h908
                · rcases m.htr 0 2 4 (by decide) (by decide) with h909 | h909
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h910 | h910
                    · linarith only [h895, h908, h910, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h910, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h913 | h913
                    · linarith only [h895, h908, h913, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h913, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h855, h908, hlam]
            · linarith only [h897, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h918 | h918
            · rcases m.htr 0 1 3 (by decide) (by decide) with h919 | h919
              · rcases m.htr 0 1 5 (by decide) (by decide) with h920 | h920
                · rcases m.htr 0 2 4 (by decide) (by decide) with h921 | h921
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h922 | h922
                    · linarith only [h895, h920, h922, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h922, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h925 | h925
                    · linarith only [h895, h920, h925, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h925, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h855, h920, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h929 | h929
                · rcases m.htr 0 2 4 (by decide) (by decide) with h930 | h930
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h931 | h931
                    · linarith only [h895, h929, h931, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h931, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h934 | h934
                    · linarith only [h895, h929, h934, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h934, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h855, h929, hlam]
            · linarith only [h918, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h939 | h939
          · rcases p0_3 (m.d 4 5) (by simp) with h940 | h940
            · rcases m.htr 0 1 3 (by decide) (by decide) with h941 | h941
              · rcases m.htr 0 1 5 (by decide) (by decide) with h942 | h942
                · rcases m.htr 0 2 4 (by decide) (by decide) with h943 | h943
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h944 | h944
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h945 | h945
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h946 | h946
                        · linarith only [h939, h942, h946, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h946, hc03, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h949 | h949
                        · linarith only [h939, h942, h949, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h949, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h895, h944, hlam]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h953 | h953
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h954 | h954
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h955 | h955
                        · linarith only [h939, h942, h955, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h955, hc03, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h958 | h958
                        · linarith only [h939, h942, h958, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h958, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h895, h953, hlam]
                · linarith only [h855, h942, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h963 | h963
                · rcases m.htr 0 2 4 (by decide) (by decide) with h964 | h964
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h965 | h965
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h966 | h966
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h967 | h967
                        · linarith only [h939, h963, h967, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h967, hc03, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h970 | h970
                        · linarith only [h939, h963, h964, h966, h970, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                        · linarith only [h970, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h895, h965, hlam]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h974 | h974
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h975 | h975
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h976 | h976
                        · linarith only [h939, h963, h976, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h976, hc03, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h979 | h979
                        · linarith only [h939, h963, h979, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h979, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h895, h974, hlam]
                · linarith only [h855, h963, hlam]
            · linarith only [h940, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h985 | h985
            · rcases m.htr 0 1 3 (by decide) (by decide) with h986 | h986
              · rcases m.htr 0 1 5 (by decide) (by decide) with h987 | h987
                · rcases m.htr 0 2 4 (by decide) (by decide) with h988 | h988
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h989 | h989
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h990 | h990
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h991 | h991
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h992 | h992
                          · linarith only [h992, hlam, p0_0]
                          · linarith only [h992, hc04, hc45, hlam, hphi, p0_1]
                        · linarith only [h939, h991, hlam]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h996 | h996
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h997 | h997
                          · linarith only [h997, hlam, p0_0]
                          · linarith only [h990, h997, hc03, hc45, hlam, hphi, ht34, p0_1]
                        · linarith only [h939, h996, hlam]
                    · linarith only [h895, h989, hlam]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1002 | h1002
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1003 | h1003
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1004 | h1004
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h1005 | h1005
                          · linarith only [h1005, hlam, p0_0]
                          · linarith only [h1002, h1005, h988, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1]
                        · linarith only [h1004, h939, hlam]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1009 | h1009
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h1010 | h1010
                          · linarith only [h1010, hlam, p0_0]
                          · linarith only [h1003, h1010, hc03, hc45, hlam, hphi, ht34, p0_1]
                        · linarith only [h1009, h939, hlam]
                    · linarith only [h1002, h895, hlam]
                · linarith only [h855, h987, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1016 | h1016
                · rcases m.htr 0 2 4 (by decide) (by decide) with h1017 | h1017
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1018 | h1018
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1019 | h1019
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1020 | h1020
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h1021 | h1021
                          · linarith only [h1021, hlam, p0_0]
                          · linarith only [h1017, h1021, hc24, hc45, hlam, hphi, p0_1]
                        · linarith only [h1020, h939, hlam]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1025 | h1025
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h1026 | h1026
                          · linarith only [h1026, hlam, p0_0]
                          · linarith only [h1019, h1026, h986, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                        · linarith only [h1025, h939, hlam]
                    · linarith only [h1018, h895, hlam]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1031 | h1031
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1032 | h1032
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1033 | h1033
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h1034 | h1034
                          · linarith only [h1034, hlam, p0_0]
                          · linarith only [h1017, h1031, h1034, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1]
                        · linarith only [h1033, h939, hlam]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1038 | h1038
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h1039 | h1039
                          · linarith only [h1039, hlam, p0_0]
                          · linarith only [h1032, h1039, hc03, hc45, hlam, hphi, ht34, p0_1]
                        · linarith only [h1038, h939, hlam]
                    · linarith only [h1031, h895, hlam]
                · linarith only [h1016, h855, hlam]
            · linarith only [h985, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h1046 | h1046
    · linarith only [h1046, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h1048 | h1048
      · linarith only [h1048, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h1050 | h1050
        · rcases p0_3 (m.d 3 5) (by simp) with h1051 | h1051
          · rcases p0_3 (m.d 4 5) (by simp) with h1052 | h1052
            · rcases m.htr 0 1 3 (by decide) (by decide) with h1053 | h1053
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1054 | h1054
                · linarith only [h1046, h1054, hlam]
                · linarith only [h1050, h1054, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1057 | h1057
                · linarith only [h1046, h1057, hlam]
                · linarith only [h1057, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1052, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1061 | h1061
            · rcases m.htr 0 1 3 (by decide) (by decide) with h1062 | h1062
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1063 | h1063
                · linarith only [h1046, h1063, hlam]
                · linarith only [h1062, h1063, hc13, hc45, hlam, hphi, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1066 | h1066
                · linarith only [h1046, h1066, hlam]
                · linarith only [h1066, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1061, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1070 | h1070
          · rcases p0_3 (m.d 4 5) (by simp) with h1071 | h1071
            · rcases m.htr 0 1 3 (by decide) (by decide) with h1072 | h1072
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1073 | h1073
                · linarith only [h1046, h1073, hlam]
                · linarith only [h1072, h1073, hc13, hc45, hlam, hphi, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1076 | h1076
                · linarith only [h1046, h1076, hlam]
                · linarith only [h1076, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1071, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1080 | h1080
            · rcases m.htr 0 1 3 (by decide) (by decide) with h1081 | h1081
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1082 | h1082
                · linarith only [h1046, h1082, hlam]
                · linarith only [h1082, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1085 | h1085
                · linarith only [h1046, h1085, hlam]
                · linarith only [h1085, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1080, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h1089 | h1089
    · linarith only [h1089, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h1091 | h1091
      · rcases p0_3 (m.d 2 5) (by simp) with h1092 | h1092
        · linarith only [h1092, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1094 | h1094
          · rcases p0_3 (m.d 4 5) (by simp) with h1095 | h1095
            · rcases m.htr 0 1 3 (by decide) (by decide) with h1096 | h1096
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1097 | h1097
                · linarith only [h1091, h1097, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h1089, h1094, h1097, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1100 | h1100
                · linarith only [h1089, h1091, h1100, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h1089, h1100, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1095, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1104 | h1104
            · rcases m.htr 0 1 3 (by decide) (by decide) with h1105 | h1105
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1106 | h1106
                · linarith only [h1089, h1091, h1106, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h1089, h1105, h1106, hc13, hc45, hlam, hphi, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1109 | h1109
                · linarith only [h1089, h1091, h1109, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h1089, h1109, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1104, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h1113 | h1113
        · linarith only [h1113, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1115 | h1115
          · rcases p0_3 (m.d 4 5) (by simp) with h1116 | h1116
            · rcases m.htr 0 1 3 (by decide) (by decide) with h1117 | h1117
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1118 | h1118
                · rcases m.htr 0 2 4 (by decide) (by decide) with h1119 | h1119
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1120 | h1120
                    · linarith only [h1089, h1120, hlam]
                    · linarith only [h1120, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1123 | h1123
                    · linarith only [h1089, h1123, hlam]
                    · linarith only [h1123, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h1091, h1118, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1127 | h1127
                · rcases m.htr 0 2 4 (by decide) (by decide) with h1128 | h1128
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1129 | h1129
                    · linarith only [h1089, h1129, hlam]
                    · linarith only [h1128, h1129, hc24, hc45, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1132 | h1132
                    · linarith only [h1089, h1132, hlam]
                    · linarith only [h1132, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h1091, h1127, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1116, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1137 | h1137
            · rcases m.htr 0 1 3 (by decide) (by decide) with h1138 | h1138
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1139 | h1139
                · rcases m.htr 0 2 4 (by decide) (by decide) with h1140 | h1140
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1141 | h1141
                    · linarith only [h1089, h1141, hlam]
                    · linarith only [h1140, h1141, hc24, hc45, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1144 | h1144
                    · linarith only [h1089, h1144, hlam]
                    · linarith only [h1144, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h1091, h1138, h1139, hc13, hc45, hlam, hphi, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1148 | h1148
                · rcases m.htr 0 2 4 (by decide) (by decide) with h1149 | h1149
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1150 | h1150
                    · linarith only [h1089, h1150, hlam]
                    · linarith only [h1149, h1150, hc24, hc45, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1153 | h1153
                    · linarith only [h1089, h1153, hlam]
                    · linarith only [h1153, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h1091, h1148, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1137, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h1158 | h1158
    · linarith only [h1158, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h1160 | h1160
      · rcases p0_3 (m.d 2 5) (by simp) with h1161 | h1161
        · rcases p0_3 (m.d 3 5) (by simp) with h1162 | h1162
          · linarith only [h1162, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1164 | h1164
            · rcases m.htr 0 1 3 (by decide) (by decide) with h1165 | h1165
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1166 | h1166
                · linarith only [h1160, h1166, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h1158, h1161, h1166, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1169 | h1169
                · linarith only [h1158, h1160, h1169, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h1158, h1169, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1164, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1173 | h1173
          · linarith only [h1173, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1175 | h1175
            · rcases m.htr 0 1 3 (by decide) (by decide) with h1176 | h1176
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1177 | h1177
                · linarith only [h1158, h1160, h1177, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h1158, h1177, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1180 | h1180
                · linarith only [h1158, h1160, h1180, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h1158, h1180, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1175, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h1184 | h1184
        · rcases p0_3 (m.d 3 5) (by simp) with h1185 | h1185
          · linarith only [h1185, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1187 | h1187
            · rcases m.htr 0 1 3 (by decide) (by decide) with h1188 | h1188
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1189 | h1189
                · rcases m.htr 0 2 4 (by decide) (by decide) with h1190 | h1190
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1191 | h1191
                    · linarith only [h1158, h1184, h1189, h1191, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1158, h1191, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1194 | h1194
                    · linarith only [h1158, h1184, h1190, h1194, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                    · linarith only [h1158, h1194, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h1160, h1189, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1198 | h1198
                · rcases m.htr 0 2 4 (by decide) (by decide) with h1199 | h1199
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1200 | h1200
                    · linarith only [h1158, h1184, h1200, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1158, h1200, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1203 | h1203
                    · linarith only [h1158, h1184, h1199, h1203, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                    · linarith only [h1158, h1203, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h1160, h1198, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1187, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1208 | h1208
          · linarith only [h1208, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1210 | h1210
            · rcases m.htr 0 1 3 (by decide) (by decide) with h1211 | h1211
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1212 | h1212
                · rcases m.htr 0 2 4 (by decide) (by decide) with h1213 | h1213
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1214 | h1214
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1215 | h1215
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1216 | h1216
                        · linarith only [h1158, h1216, hlam]
                        · linarith only [h1215, h1216, hc34, hc45, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1219 | h1219
                        · linarith only [h1158, h1219, hlam]
                        · linarith only [h1219, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h1184, h1214, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1223 | h1223
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1224 | h1224
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1225 | h1225
                        · linarith only [h1158, h1225, hlam]
                        · linarith only [h1224, h1225, hc34, hc45, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1228 | h1228
                        · linarith only [h1158, h1228, hlam]
                        · linarith only [h1228, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h1184, h1223, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h1160, h1211, h1212, hc13, hc45, hlam, hphi, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1233 | h1233
                · rcases m.htr 0 2 4 (by decide) (by decide) with h1234 | h1234
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1235 | h1235
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1236 | h1236
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1237 | h1237
                        · linarith only [h1158, h1237, hlam]
                        · linarith only [h1237, hc03, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1240 | h1240
                        · linarith only [h1158, h1240, hlam]
                        · linarith only [h1211, h1240, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h1184, h1234, h1235, hc24, hc45, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1244 | h1244
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1245 | h1245
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1246 | h1246
                        · linarith only [h1158, h1246, hlam]
                        · linarith only [h1234, h1245, h1246, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1249 | h1249
                        · linarith only [h1158, h1249, hlam]
                        · linarith only [h1211, h1233, h1249, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1]
                    · linarith only [h1184, h1244, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h1160, h1233, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1210, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT2_M_LI_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h5ehi := hb5.2.1
  have h2elo := hb2.1
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
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
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
                          · linarith only [h12, h6, hc12, hlam, hphi, u2elo0]
                        · linarith only [h10, h11, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h10, h4, hc12, hlam, hphi, u2elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h18 | h18
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
                          · linarith only [h0, h19, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                          · linarith only [h19, h6, hc12, hlam, hphi, u2elo0]
                        · linarith only [h17, h18, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h17, h4, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h24 | h24
                    · linarith only [h24, h7, h8, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
                          · linarith only [h0, h28, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                          · linarith only [h26, h28, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h26, h27, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h26, h4, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h33 | h33
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h34 | h34
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h37 | h37
                          · linarith only [h0, h37, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                          · linarith only [h37, h6, hc12, hlam, hphi, u2elo0]
                        · linarith only [h35, h36, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h35, h4, hc12, hlam, hphi, u2elo0]
                    · linarith only [h33, h34, h7, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h43 | h43
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                          · linarith only [h0, h46, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                          · linarith only [h46, h6, hc12, hlam, hphi, u2elo0]
                        · linarith only [h44, h45, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h4, h44, hc12, hlam, hphi, u2elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h51 | h51
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
                          · linarith only [h0, h53, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                          · linarith only [h53, h6, hc12, hlam, hphi, u2elo0]
                        · linarith only [h5, h51, h52, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h4, h51, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h58 | h58
                · rcases m.htr 0 3 5 (by decide) (by decide) with h59 | h59
                  · linarith only [h4, h59, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h61 | h61
                    · linarith only [h4, h58, h6, h61, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h65 | h65
                          · linarith only [h6, h65, hc02, hlam, hphi, u2elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h67 | h67
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
                              · linarith only [h1, h59, h68, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
                                · linarith only [h2, h61, h70, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h72 | h72
                                  · linarith only [h0, h6, h63, h72, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                                  · linarith only [h4, h58, h6, h72, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                            · linarith only [h4, h58, h6, h67, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h5, h6, h64, hc12, hlam, hphi, u2elo4]
                      · linarith only [h4, h6, h63, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h78 | h78
                  · linarith only [h4, h6, h78, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h80 | h80
                    · linarith only [h5, h6, h80, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h82 | h82
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h83 | h83
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h84 | h84
                          · linarith only [h6, h84, hc02, hlam, hphi, u2elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
                            · linarith only [h1, h58, h86, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                              · linarith only [h1, h78, h88, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                                · linarith only [h2, h80, h90, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                                  · linarith only [h0, h58, h6, h82, h92, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                                    · linarith only [h1, h78, h82, h94, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                                      · linarith only [h0, h58, h6, h80, h83, h96, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                                        · linarith only [h4, h6, h96, h98, hc23, hc34, hlam, hphi]
                                        · rcases h0bigk with h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h0, h83, h92, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            rcases p100_3 (m.d 0 1) (by simp) with h103 | h103
                                            · rcases p100_3 (m.d 0 2) (by simp) with h104 | h104
                                              · linarith only [h0, h104, hlam]
                                              · linarith only [h104, h4, hlam]
                                            · linarith only [h1, h103, hlam]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            rcases p100_3 (m.d 0 1) (by simp) with h108 | h108
                                            · rcases p100_3 (m.d 0 2) (by simp) with h109 | h109
                                              · linarith only [h0, h109, hlam]
                                              · linarith only [h109, h5, hlam]
                                            · linarith only [h108, h2, hlam]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h0, h6, h83, h92, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h0, hlam, p100_1]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h1, h6, h82, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p100_1, u2elo4]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h1, h58, h6, h82, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p100_1, u2elo4]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h6, hlam, p100_1]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h1, hlam, p100_1]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h4, hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h58, hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h78, hlam, p100_1]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h2, hlam, p100_1]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h5, hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h1, h5, h6, h82, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p100_1, u2elo4]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h80, hlam, p100_1]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h3, hlam, p100_1]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h0, h83, h92, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo4]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            rcases p100_3 (m.d 0 1) (by simp) with h131 | h131
                                            · rcases p100_3 (m.d 0 2) (by simp) with h132 | h132
                                              · linarith only [h132, h6, hlam]
                                              · linarith only [h132, h4, hlam]
                                            · linarith only [h1, h131, hlam]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            rcases p100_3 (m.d 0 1) (by simp) with h136 | h136
                                            · rcases p100_3 (m.d 0 2) (by simp) with h137 | h137
                                              · linarith only [h137, h6, hlam]
                                              · linarith only [h137, h5, hlam]
                                            · linarith only [h136, h2, hlam]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [hlam, p100_0]
                        · linarith only [h5, h83, hc12, hlam, hphi, u2elo0]
                      · linarith only [h4, h82, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h144 | h144
              · linarith only [h144, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h146 | h146
                · linarith only [h146, h4, h5, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h148 | h148
                  · linarith only [h148, h4, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h150 | h150
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h151 | h151
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h152 | h152
                        · linarith only [h152, h5, hc02, hlam, hphi, u2elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h154 | h154
                          · linarith only [h0, h144, h154, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h156 | h156
                            · linarith only [h0, h146, h150, h151, h156, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h158 | h158
                              · linarith only [h0, h148, h151, h158, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h160 | h160
                                · linarith only [h160, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                                · linarith only [h150, h152, h160, h5, hc12, hlam, hphi, u2elo3]
                      · linarith only [h151, h4, h5, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h164 | h164
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h165 | h165
                        · linarith only [h0, h165, h5, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h167 | h167
                          · linarith only [h0, h144, h167, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h169 | h169
                            · linarith only [h0, h1, h146, h164, h169, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h171 | h171
                              · linarith only [h1, h148, h171, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h173 | h173
                                · linarith only [h173, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                                  · linarith only [h0, h146, h164, h175, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h177 | h177
                                    · linarith only [h1, h148, h164, h177, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h179 | h179
                                      · linarith only [h0, h150, h164, h179, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                                      · linarith only [h0, h164, h179, h5, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h164, h4, h5, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h183 | h183
            · rcases m.htr 0 2 5 (by decide) (by decide) with h184 | h184
              · linarith only [h184, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h186 | h186
                · rcases m.htr 0 3 5 (by decide) (by decide) with h187 | h187
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h188 | h188
                    · linarith only [h183, h188, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h190 | h190
                      · linarith only [h190, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h192 | h192
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h193 | h193
                          · linarith only [h0, h184, h193, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h195 | h195
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h196 | h196
                              · linarith only [h1, h196, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                              · linarith only [h187, h195, h196, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h186, h190, h192, h195, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                        · linarith only [h183, h184, h192, hc12, hlam, hphi, u2elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h201 | h201
                    · linarith only [h183, h184, h201, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h203 | h203
                      · linarith only [h0, h203, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h205 | h205
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h206 | h206
                          · linarith only [h0, h184, h206, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h208 | h208
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h209 | h209
                              · linarith only [h1, h187, h209, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h211 | h211
                                · linarith only [h183, h184, h2, h201, h211, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h213 | h213
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h214 | h214
                                    · linarith only [h187, h214, h4, hc02, hlam, hphi, u2elo2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h216 | h216
                                      · linarith only [h0, h201, h205, h216, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h218 | h218
                                        · linarith only [h213, h214, h216, h218, h4, hc02, hlam, hphi, u2elo3]
                                        · linarith only [h0, h205, h213, h214, h218, h4, hc34, hc45, hlam, hphi]
                                  · linarith only [h186, h213, h4, hlam]
                            · linarith only [h186, h187, h208, hc13, hc35, hlam, hphi]
                        · linarith only [h183, h205, h4, hc12, hlam, hphi, u2elo2]
                · linarith only [h183, h186, h4, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h225 | h225
              · linarith only [h225, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h227 | h227
                · rcases m.htr 0 3 5 (by decide) (by decide) with h228 | h228
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h229 | h229
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h230 | h230
                      · linarith only [h230, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h232 | h232
                        · linarith only [h0, h183, h229, h232, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h234 | h234
                          · linarith only [h0, h225, h234, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h236 | h236
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h237 | h237
                              · linarith only [h1, h237, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                              · linarith only [h228, h236, h237, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h227, h230, h236, h4, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h241 | h241
                      · linarith only [h241, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h243 | h243
                        · linarith only [h0, h183, h243, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h245 | h245
                          · linarith only [h0, h225, h245, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h247 | h247
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h248 | h248
                              · linarith only [h1, h248, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                              · linarith only [h228, h241, h248, h4, hc12, hlam, hphi, u2elo2]
                            · linarith only [h227, h241, h247, h4, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h252 | h252
                    · linarith only [h227, h228, h252, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h254 | h254
                      · linarith only [h254, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
                        · linarith only [h0, h183, h256, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h258 | h258
                          · linarith only [h0, h183, h225, h258, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h260 | h260
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h261 | h261
                              · linarith only [h1, h228, h261, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h263 | h263
                                · linarith only [h2, h252, h263, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h265 | h265
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h266 | h266
                                    · linarith only [h1, h228, h260, h266, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h268 | h268
                                      · linarith only [h183, h252, h268, hc02, hlam, hphi, u2elo3]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h270 | h270
                                        · linarith only [h1, h260, h268, h270, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                        · rcases h0bigk with h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [hlam, p272_0]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            rcases p272_3 (m.d 0 1) (by simp) with h274 | h274
                                            · rcases p272_3 (m.d 0 2) (by simp) with h275 | h275
                                              · linarith only [h0, h275, hlam]
                                              · rcases p272_3 (m.d 0 3) (by simp) with h277 | h277
                                                · linarith only [h1, h277, hlam]
                                                · linarith only [h277, h4, hlam]
                                            · linarith only [h0, h274, hlam]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [h227, hc34, hlam, hphi, ht0b, ht45, ht5b, p272_1, u0elo0]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            rcases p272_3 (m.d 0 1) (by simp) with h282 | h282
                                            · rcases p272_3 (m.d 0 2) (by simp) with h283 | h283
                                              · linarith only [h0, h283, hlam]
                                              · rcases p272_3 (m.d 0 3) (by simp) with h285 | h285
                                                · linarith only [h1, h285, hlam]
                                                · linarith only [h227, h285, hlam]
                                            · linarith only [h2, h282, hlam]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [hlam, hphi, ht0b, ht5b, p272_1, u0elo0, u5ehi0]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [h0, hlam, p272_1]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [hlam, p272_0]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [h4, hlam, p272_1]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [h183, hlam, p272_1]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [h225, hlam, p272_1]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [h1, hlam, p272_1]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [h266, h270, h4, hc02, hc45, hlam, hphi, ht23, ht34, p272_1]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [hlam, p272_0]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [h266, h270, h4, hc04, hc45, hlam, hphi, p272_1]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [h228, hlam, p272_1]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [h2, hlam, p272_1]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [h0, h183, hc12, hlam, hphi, p272_1, u2elo3]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [h227, hlam, p272_1]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [hlam, p272_0]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [h252, hlam, p272_1]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [h3, hlam, p272_1]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [h0, h225, hc12, hlam, hphi, p272_1, u2elo4]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [h1, h225, h260, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p272_1, u2elo4]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [h0, h183, h225, hc12, hlam, hphi, p272_1, u2elo4]
                                          · have p272_0 := h272c.1
                                            have p272_1 := h272c.2.1
                                            have p272_2 := h272c.2.2.1
                                            have p272_3 := h272c.2.2.2
                                            linarith only [hlam, p272_0]
                                  · linarith only [h1, h260, h265, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h227, h254, h260, h4, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h312 | h312
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h313 | h313
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h314 | h314
                      · linarith only [h0, h314, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h316 | h316
                        · linarith only [h0, h183, h227, h312, h316, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h318 | h318
                          · linarith only [h0, h225, h318, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h320 | h320
                            · linarith only [h1, h227, h312, h320, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h322 | h322
                              · linarith only [h1, h322, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                              · linarith only [h227, h312, h322, hc13, hc34, hlam, hphi]
                    · linarith only [h227, h312, h313, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h326 | h326
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h327 | h327
                      · linarith only [h0, h327, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h329 | h329
                        · linarith only [h0, h183, h329, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h331 | h331
                          · linarith only [h0, h225, h331, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h333 | h333
                            · linarith only [h1, h227, h333, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h335 | h335
                              · linarith only [h1, h312, h335, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h337 | h337
                                · linarith only [h2, h337, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                                · linarith only [h183, h326, h329, h337, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h340 | h340
                      · linarith only [h0, h340, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h342 | h342
                        · linarith only [h0, h183, h342, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h344 | h344
                          · linarith only [h0, h225, h344, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h346 | h346
                            · linarith only [h1, h227, h346, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h348 | h348
                              · linarith only [h1, h312, h348, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h350 | h350
                                · linarith only [h2, h350, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h352 | h352
                                  · linarith only [h227, h352, h4, hc02, hlam, hphi, u2elo2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h354 | h354
                                    · linarith only [h0, h312, h352, h354, h4, hc12, hlam, hphi, u2elo3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h356 | h356
                                      · linarith only [h0, h227, h326, h356, h4, hc12, hlam, hphi, u2elo3]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h358 | h358
                                        · linarith only [h0, h352, h356, h358, h4, hc12, hc34, hlam, hphi, ht23]
                                        · linarith only [h0, h352, h358, h4, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h361 | h361
          · rcases m.htr 0 2 4 (by decide) (by decide) with h362 | h362
            · rcases m.htr 0 2 5 (by decide) (by decide) with h363 | h363
              · linarith only [h0, h3, h363, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h365 | h365
                · rcases m.htr 0 3 5 (by decide) (by decide) with h366 | h366
                  · linarith only [h361, h363, h366, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h368 | h368
                    · linarith only [h362, h363, h368, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h371 | h371
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h372 | h372
                          · linarith only [h0, h3, h363, h372, hlam]
                          · linarith only [h0, h3, h370, h372, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h362, h363, h370, h371, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h361, h363, h370, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h377 | h377
                  · linarith only [h362, h363, h365, h377, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h379 | h379
                    · linarith only [h362, h363, h379, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h381 | h381
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h382 | h382
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h383 | h383
                          · linarith only [h0, h363, h383, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h0, h3, h381, h383, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h362, h381, h382, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h361, h363, h381, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h388 | h388
              · linarith only [h362, h388, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h390 | h390
                · linarith only [h361, h362, h390, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h392 | h392
                  · linarith only [h361, h362, h392, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h394 | h394
                    · linarith only [h2, h3, h394, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h396 | h396
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h397 | h397
                        · linarith only [h362, h397, hc02, hlam, hphi, u2elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h399 | h399
                          · linarith only [h0, h3, h362, h388, h399, hc01, hlam, hphi, ht12, u2elo3]
                          · linarith only [h2, h3, h397, h399, hc12, hlam, hphi, u2elo4]
                      · linarith only [h361, h396, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h403 | h403
            · rcases m.htr 0 2 5 (by decide) (by decide) with h404 | h404
              · linarith only [h361, h404, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h406 | h406
                · rcases m.htr 0 3 5 (by decide) (by decide) with h407 | h407
                  · linarith only [h1, h3, h407, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h409 | h409
                    · linarith only [h361, h403, h409, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h411 | h411
                      · linarith only [h361, h411, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h413 | h413
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h414 | h414
                          · linarith only [h0, h3, h404, h414, hlam]
                          · linarith only [h1, h3, h411, h413, h414, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · linarith only [h361, h403, h413, hc12, hlam, hphi, u2elo2]
                · linarith only [h361, h403, h406, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h419 | h419
              · linarith only [h361, h419, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h421 | h421
                · rcases m.htr 0 3 5 (by decide) (by decide) with h422 | h422
                  · linarith only [h1, h3, h422, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h424 | h424
                    · linarith only [h2, h3, h424, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h426 | h426
                      · linarith only [h361, h426, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h428 | h428
                        · linarith only [h0, h403, h428, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h430 | h430
                          · linarith only [h0, h3, h403, h419, h430, hc01, hlam, hphi, ht12, u2elo3]
                          · linarith only [h0, h3, h430, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h433 | h433
                  · linarith only [h2, h3, h421, h433, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h435 | h435
                    · linarith only [h2, h3, h435, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h437 | h437
                      · linarith only [h361, h437, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h439 | h439
                        · linarith only [h0, h403, h439, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h441 | h441
                          · linarith only [h1, h437, h441, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                          · linarith only [h0, h3, h441, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h444 | h444
        · rcases m.htr 0 2 3 (by decide) (by decide) with h445 | h445
          · rcases m.htr 0 2 4 (by decide) (by decide) with h446 | h446
            · linarith only [h0, h2, h446, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h448 | h448
              · linarith only [h446, h448, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h450 | h450
                · linarith only [h2, h444, h445, h446, h450, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h452 | h452
                  · linarith only [h445, h446, h452, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h454 | h454
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h455 | h455
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h456 | h456
                        · linarith only [h0, h446, h456, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h0, h2, h455, h456, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h445, h448, h455, hc12, hlam, hphi, u2elo4]
                    · linarith only [h2, h444, h454, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h461 | h461
            · linarith only [h2, h444, h445, h461, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h463 | h463
              · linarith only [h445, h463, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h465 | h465
                · linarith only [h1, h2, h465, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h467 | h467
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h468 | h468
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h469 | h469
                      · linarith only [h445, h469, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h471 | h471
                        · linarith only [h0, h461, h468, h471, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                        · linarith only [h1, h2, h467, h471, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                    · linarith only [h1, h2, h467, h468, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h475 | h475
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h476 | h476
                      · linarith only [h0, h445, h476, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h478 | h478
                        · linarith only [h0, h461, h475, h478, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                        · linarith only [h1, h2, h476, h478, hc12, hlam, hphi, u2elo3]
                    · linarith only [h2, h444, h475, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h482 | h482
          · rcases m.htr 0 2 4 (by decide) (by decide) with h483 | h483
            · linarith only [h0, h2, h483, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h485 | h485
              · linarith only [h483, h485, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h487 | h487
                · linarith only [h0, h2, h482, h483, h487, hc12, hlam, hphi, u2elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h489 | h489
                  · linarith only [h482, h483, h489, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h491 | h491
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h492 | h492
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h493 | h493
                        · linarith only [h0, h483, h493, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h0, h2, h492, h493, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h482, h492, hc12, hlam, hphi, u2elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h497 | h497
                      · linarith only [h0, h2, h491, h497, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h482, h483, h497, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h500 | h500
            · linarith only [h0, h2, h482, h500, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h502 | h502
              · linarith only [h500, h502, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h504 | h504
                · linarith only [h1, h2, h504, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h506 | h506
                  · linarith only [h1, h444, h506, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h508 | h508
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h509 | h509
                      · linarith only [h0, h482, h509, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h511 | h511
                        · linarith only [h0, h444, h500, h508, h511, hlam]
                        · linarith only [h1, h2, h509, h511, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h514 | h514
                      · linarith only [h482, h514, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h516 | h516
                        · linarith only [h0, h2, h508, h516, hc24, hc45, hlam, hphi]
                        · linarith only [h1, h2, h514, h516, hc12, hlam, hphi, u2elo3]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h519 | h519
      · rcases m.htr 0 1 5 (by decide) (by decide) with h520 | h520
        · rcases m.htr 0 2 3 (by decide) (by decide) with h521 | h521
          · linarith only [h0, h1, h521, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h523 | h523
            · rcases m.htr 0 2 5 (by decide) (by decide) with h524 | h524
              · linarith only [h521, h524, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h526 | h526
                · rcases m.htr 0 3 5 (by decide) (by decide) with h527 | h527
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h528 | h528
                    · linarith only [h521, h523, h528, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h530 | h530
                      · linarith only [h521, h530, hc02, hlam, hphi, u2elo1]
                      · linarith only [h1, h520, h530, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                  · linarith only [h1, h520, h527, hlam]
                · linarith only [h1, h520, h521, h523, h526, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h535 | h535
              · linarith only [h521, h535, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h537 | h537
                · rcases m.htr 0 3 5 (by decide) (by decide) with h538 | h538
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h539 | h539
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h540 | h540
                      · linarith only [h0, h521, h540, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h540, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h543 | h543
                      · linarith only [h0, h521, h538, h543, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                      · linarith only [h1, h520, h543, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                  · linarith only [h1, h520, h538, hlam]
                · linarith only [h1, h519, h537, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h548 | h548
          · linarith only [h0, h1, h548, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h550 | h550
            · rcases m.htr 0 2 5 (by decide) (by decide) with h551 | h551
              · linarith only [h548, h551, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h553 | h553
                · rcases m.htr 0 3 5 (by decide) (by decide) with h554 | h554
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h555 | h555
                    · linarith only [h548, h550, h555, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h557 | h557
                      · linarith only [h0, h548, h557, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h557, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h560 | h560
                    · linarith only [h548, h550, h560, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h562 | h562
                      · linarith only [h548, h562, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1, h562, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h1, h550, h553, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h566 | h566
              · linarith only [h550, h566, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h568 | h568
                · rcases m.htr 0 3 5 (by decide) (by decide) with h569 | h569
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h570 | h570
                    · linarith only [h519, h520, h570, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h572 | h572
                      · linarith only [h548, h569, h572, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                      · linarith only [h0, h1, h572, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h575 | h575
                    · linarith only [h1, h519, h569, h575, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h577 | h577
                      · linarith only [h0, h1, h569, h577, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h1, h577, hc12, hlam, hphi, u2elo2]
                · linarith only [h1, h519, h568, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h581 | h581
        · rcases m.htr 0 2 3 (by decide) (by decide) with h582 | h582
          · linarith only [h0, h1, h582, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h584 | h584
            · linarith only [h519, h581, h582, h584, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h586 | h586
              · linarith only [h582, h586, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h588 | h588
                · rcases m.htr 0 3 5 (by decide) (by decide) with h589 | h589
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h590 | h590
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h591 | h591
                      · linarith only [h582, h591, hc02, hlam, hphi, u2elo1]
                      · linarith only [h1, h581, h591, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                    · linarith only [h519, h581, h590, hlam]
                  · linarith only [h519, h581, h588, h589, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h596 | h596
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h597 | h597
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h598 | h598
                      · linarith only [h0, h1, h588, h598, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h1, h598, hc12, hlam, hphi, u2elo2]
                    · linarith only [h519, h581, h597, hlam]
                  · linarith only [h1, h581, h596, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h603 | h603
          · linarith only [h0, h1, h603, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h605 | h605
            · linarith only [h0, h519, h603, h605, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h607 | h607
              · linarith only [h603, h607, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h609 | h609
                · rcases m.htr 0 3 5 (by decide) (by decide) with h610 | h610
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h611 | h611
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h612 | h612
                      · linarith only [h0, h603, h612, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h612, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h615 | h615
                      · linarith only [h0, h603, h610, h615, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                      · linarith only [h0, h1, h615, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h618 | h618
                    · linarith only [h609, h610, h618, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h620 | h620
                      · linarith only [h0, h1, h610, h620, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h1, h620, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h623 | h623
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h624 | h624
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h625 | h625
                      · linarith only [h0, h581, h609, h623, h625, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h1, h625, hc12, hlam, hphi, u2elo2]
                    · linarith only [h609, h623, h624, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h629 | h629
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h630 | h630
                      · linarith only [h0, h1, h609, h630, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h1, h630, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h633 | h633
                      · linarith only [h0, h1, h609, h633, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h1, h633, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h636 | h636
    · rcases m.htr 0 1 4 (by decide) (by decide) with h637 | h637
      · rcases m.htr 0 1 5 (by decide) (by decide) with h638 | h638
        · linarith only [h0, h638, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h640 | h640
          · rcases m.htr 0 2 4 (by decide) (by decide) with h641 | h641
            · rcases m.htr 0 2 5 (by decide) (by decide) with h642 | h642
              · rcases m.htr 0 3 4 (by decide) (by decide) with h643 | h643
                · rcases m.htr 0 3 5 (by decide) (by decide) with h644 | h644
                  · linarith only [h0, h636, h644, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h646 | h646
                    · linarith only [h0, h636, h643, h646, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h648 | h648
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h649 | h649
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h650 | h650
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h651 | h651
                            · linarith only [h636, h638, h650, h651, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h636, h638, h643, h650, h651, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h642, h650, hc12, hlam, hphi, u2elo0]
                        · linarith only [h0, h642, h649, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                      · linarith only [h0, h648, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h657 | h657
                  · linarith only [h0, h637, h643, h657, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h659 | h659
                    · linarith only [h0, h637, h659, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h661 | h661
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h662 | h662
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h663 | h663
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h664 | h664
                            · linarith only [h636, h638, h643, h663, h664, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h666 | h666
                              · linarith only [h636, h638, h657, h663, h666, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h668 | h668
                                · linarith only [h637, h638, h643, h659, h663, h668, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h670 | h670
                                  · linarith only [h636, h643, h661, h670, hlam]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h672 | h672
                                    · linarith only [h636, h637, h638, h661, h666, h672, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h674 | h674
                                      · linarith only [h637, h638, h661, h664, h668, h674, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h676 | h676
                                        · linarith only [h637, h638, h661, h664, h668, h676, hc23, hc34, hlam, hphi]
                                        · rcases h0bigk with h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [hlam, p678_0]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [h0, hlam, p678_0]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [h636, h638, h661, h666, hc23, hc35, hlam, hphi, p678_1]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [h636, h638, h643, h661, h663, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p678_1, u2elo1]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [h638, hlam, p678_0]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [hc01, hlam, hphi, ht12, p678_1, u2elo0]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [hlam, p678_0]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            rcases p678_3 (m.d 0 1) (by simp) with h686 | h686
                                            · linarith only [h0, h686, hlam]
                                            · linarith only [h636, h686, hlam]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            rcases p678_3 (m.d 0 1) (by simp) with h689 | h689
                                            · linarith only [h0, h689, hlam]
                                            · linarith only [h637, h689, hlam]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [h0, h637, h638, h661, h664, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p678_1, u2elo1]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [h636, hlam, p678_1]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [h640, hlam, p678_0]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [hlam, p678_0]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [h643, hlam, p678_0]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [h657, hlam, p678_1]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [h637, hlam, p678_1]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [h641, hlam, p678_0]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [h0, h636, h637, h661, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p678_1, u2elo1]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [hlam, p678_0]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [h659, hlam, p678_1]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [h636, h661, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p678_1, u0elo4]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [h642, hlam, p678_0]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            rcases p678_3 (m.d 0 1) (by simp) with h705 | h705
                                            · linarith only [h638, h705, hlam]
                                            · linarith only [h636, h705, hlam]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            rcases p678_3 (m.d 0 1) (by simp) with h708 | h708
                                            · linarith only [h638, h708, hlam]
                                            · linarith only [h637, h708, hlam]
                                          · have p678_0 := h678c.1
                                            have p678_1 := h678c.2.1
                                            have p678_2 := h678c.2.2.1
                                            have p678_3 := h678c.2.2.2
                                            linarith only [hlam, p678_0]
                          · linarith only [h0, h663, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h642, h662, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                      · linarith only [h0, h636, h661, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h715 | h715
                · rcases m.htr 0 3 5 (by decide) (by decide) with h716 | h716
                  · linarith only [h0, h636, h716, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h718 | h718
                    · linarith only [h0, h636, h642, h715, h718, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h720 | h720
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h721 | h721
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h722 | h722
                          · linarith only [h0, h636, h642, h720, h722, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h0, h636, h720, h722, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h636, h720, h721, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h636, h720, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h727 | h727
                  · linarith only [h0, h637, h715, h727, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h729 | h729
                    · linarith only [h0, h637, h642, h729, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h731 | h731
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h732 | h732
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h733 | h733
                          · linarith only [h0, h636, h642, h731, h733, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h0, h636, h731, h733, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h636, h731, h732, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h636, h731, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · linarith only [h0, h637, h641, hlam]
          · linarith only [h0, h636, h640, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h740 | h740
        · linarith only [h0, h740, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h742 | h742
          · rcases m.htr 0 2 4 (by decide) (by decide) with h743 | h743
            · rcases m.htr 0 2 5 (by decide) (by decide) with h744 | h744
              · rcases m.htr 0 3 4 (by decide) (by decide) with h745 | h745
                · linarith only [h636, h637, h745, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h747 | h747
                  · linarith only [h0, h636, h747, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h749 | h749
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h750 | h750
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h751 | h751
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h752 | h752
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h753 | h753
                            · linarith only [h636, h637, h745, h751, h753, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h755 | h755
                              · linarith only [h636, h637, h747, h751, h755, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h757 | h757
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h758 | h758
                                  · linarith only [h740, h753, h757, h758, hc01, hlam, hphi, ht12, u2elo2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h760 | h760
                                    · linarith only [h636, h740, h750, h755, h760, hlam]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h762 | h762
                                      · linarith only [h743, h762, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h764 | h764
                                        · rcases h0bigk with h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [hlam, p765_0]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [h0, hlam, p765_0]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [h740, h753, h757, hc03, hc34, hlam, hphi, p765_1]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [h637, hlam, p765_0]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [h740, hlam, p765_0]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [h0, hc01, hlam, hphi, ht12, p765_1, u2elo1]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [hlam, p765_0]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            rcases p765_3 (m.d 0 1) (by simp) with h773 | h773
                                            · linarith only [h0, h773, hlam]
                                            · linarith only [h636, h773, hlam]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [h0, h749, h762, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p765_1, u2elo1]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [h0, h636, h740, h750, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p765_1, u2elo1]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [h636, hlam, p765_1]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [h742, hlam, p765_0]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [hlam, p765_0]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [h745, hlam, p765_0]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [h747, hlam, p765_1]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [h636, h750, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p765_1, u0elo3]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [h743, hlam, p765_0]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            rcases p765_3 (m.d 0 1) (by simp) with h785 | h785
                                            · linarith only [h637, h785, hlam]
                                            · linarith only [h636, h785, hlam]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [hlam, p765_0]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [h636, h637, h740, h750, h751, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p765_1, u2elo1]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [h636, h750, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p765_1, u0elo4]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [h744, hlam, p765_0]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            rcases p765_3 (m.d 0 1) (by simp) with h792 | h792
                                            · linarith only [h740, h792, hlam]
                                            · linarith only [h636, h792, hlam]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [h749, hlam, p765_0]
                                          · have p765_0 := h765c.1
                                            have p765_1 := h765c.2.1
                                            have p765_2 := h765c.2.2.1
                                            have p765_3 := h765c.2.2.2
                                            linarith only [hlam, p765_0]
                                        · linarith only [h745, h749, h764, hlam]
                                · linarith only [h636, h637, h750, h757, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h636, h750, h752, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h744, h751, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                      · linarith only [h0, h750, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h802 | h802
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h803 | h803
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h804 | h804
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h805 | h805
                            · linarith only [h0, h636, h745, h805, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h807 | h807
                              · linarith only [h636, h637, h803, h807, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h809 | h809
                                · linarith only [h636, h637, h749, h802, h803, h809, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                · linarith only [h636, h637, h802, h809, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h636, h802, h804, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h743, h803, hlam]
                      · linarith only [h0, h744, h802, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h815 | h815
                · linarith only [h636, h637, h815, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h817 | h817
                  · linarith only [h0, h636, h817, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h819 | h819
                    · linarith only [h743, h744, h819, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h821 | h821
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h822 | h822
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h823 | h823
                          · linarith only [h637, h743, h744, h823, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h0, h636, h821, h823, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h636, h743, h821, h822, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h636, h821, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h828 | h828
              · linarith only [h743, h828, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h830 | h830
                · linarith only [h0, h636, h743, h830, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h832 | h832
                  · linarith only [h0, h636, h743, h832, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h834 | h834
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h835 | h835
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h836 | h836
                        · linarith only [h0, h743, h836, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h636, h835, h836, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h835, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h840 | h840
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h841 | h841
                        · linarith only [h0, h636, h743, h840, h841, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h636, h840, h841, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h636, h840, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · linarith only [h0, h636, h742, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h846 | h846
      · rcases m.htr 0 1 5 (by decide) (by decide) with h847 | h847
        · linarith only [h0, h847, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h849 | h849
          · rcases m.htr 0 2 4 (by decide) (by decide) with h850 | h850
            · rcases m.htr 0 2 5 (by decide) (by decide) with h851 | h851
              · rcases m.htr 0 3 4 (by decide) (by decide) with h852 | h852
                · rcases m.htr 0 3 5 (by decide) (by decide) with h853 | h853
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h854 | h854
                    · linarith only [h0, h846, h854, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h856 | h856
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h857 | h857
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h858 | h858
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h859 | h859
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h860 | h860
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h861 | h861
                                · linarith only [h846, h847, h854, h856, h860, h861, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h863 | h863
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h864 | h864
                                    · linarith only [h849, h864, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                    · linarith only [h853, h863, h864, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                  · linarith only [h846, h847, h856, h859, h860, h863, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · linarith only [h636, h853, h860, hlam]
                            · linarith only [h636, h852, h859, hlam]
                          · linarith only [h636, h853, h856, h858, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                        · linarith only [h636, h856, h857, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h846, h856, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h873 | h873
                    · linarith only [h0, h846, h873, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h875 | h875
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h876 | h876
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h877 | h877
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h878 | h878
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h879 | h879
                              · linarith only [h636, h846, h853, h875, h876, h879, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h881 | h881
                                · linarith only [h846, h873, h881, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h883 | h883
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h884 | h884
                                    · linarith only [h636, h849, h879, h884, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h886 | h886
                                      · linarith only [h636, h846, h876, h879, h881, h886, hlam]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h888 | h888
                                        · linarith only [h636, h846, h876, h879, h881, h883, h888, hlam]
                                        · linarith only [h636, h846, h876, h879, h883, h888, hc34, hc45, hlam, hphi]
                                  · linarith only [h636, h852, h879, h883, hc23, hc35, hlam, hphi]
                            · linarith only [h636, h846, h852, h878, hlam]
                          · linarith only [h0, h851, h877, hlam]
                        · linarith only [h0, h851, h876, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                      · linarith only [h0, h875, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h636, h846, h852, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h897 | h897
                · rcases m.htr 0 3 5 (by decide) (by decide) with h898 | h898
                  · linarith only [h849, h851, h898, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h900 | h900
                    · linarith only [h0, h846, h900, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h902 | h902
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h903 | h903
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h904 | h904
                          · linarith only [h636, h849, h851, h904, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h0, h846, h903, h904, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · linarith only [h636, h902, h903, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h846, h849, h902, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h636, h846, h897, hlam]
            · linarith only [h0, h846, h850, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h911 | h911
            · rcases m.htr 0 2 5 (by decide) (by decide) with h912 | h912
              · linarith only [h849, h912, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h914 | h914
                · rcases m.htr 0 3 5 (by decide) (by decide) with h915 | h915
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h916 | h916
                    · linarith only [h0, h846, h916, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h918 | h918
                      · linarith only [h0, h849, h918, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h846, h918, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h921 | h921
                    · linarith only [h0, h846, h912, h921, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h923 | h923
                      · linarith only [h0, h849, h923, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h846, h923, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h636, h846, h914, hlam]
            · linarith only [h0, h846, h911, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h928 | h928
        · linarith only [h0, h928, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h930 | h930
          · rcases m.htr 0 2 4 (by decide) (by decide) with h931 | h931
            · rcases m.htr 0 2 5 (by decide) (by decide) with h932 | h932
              · rcases m.htr 0 3 4 (by decide) (by decide) with h933 | h933
                · rcases m.htr 0 3 5 (by decide) (by decide) with h934 | h934
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h935 | h935
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h936 | h936
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h937 | h937
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h938 | h938
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h939 | h939
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h940 | h940
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h941 | h941
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h942 | h942
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h943 | h943
                                    · linarith only [h930, h943, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                    · linarith only [h934, h942, h943, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h946 | h946
                                    · linarith only [h933, h942, h946, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h948 | h948
                                      · linarith only [h636, h933, h936, h942, h948, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h950 | h950
                                        · linarith only [h636, h933, h936, h942, h948, h950, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                        · linarith only [h846, h935, h936, h939, h942, h950, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                · linarith only [h846, h935, h941, hlam]
                              · linarith only [h636, h934, h940, hlam]
                            · linarith only [h636, h933, h939, hlam]
                          · linarith only [h636, h934, h936, h938, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                        · linarith only [h636, h933, h935, h936, h937, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                      · linarith only [h0, h932, h936, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h959 | h959
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h960 | h960
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h961 | h961
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h962 | h962
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h963 | h963
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h964 | h964
                                · linarith only [h846, h935, h960, h964, hc01, hlam, hphi, ht12, u2elo1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h966 | h966
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h967 | h967
                                    · linarith only [h930, h967, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                    · linarith only [h934, h966, h967, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h970 | h970
                                    · linarith only [h0, h930, h933, h966, h970, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h972 | h972
                                      · linarith only [h0, h930, h933, h964, h966, h972, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h974 | h974
                                        · linarith only [h0, h846, h930, h933, h964, h974, hc01, hlam, hphi, ht12, u2elo1]
                                        · rcases h0bigk with h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [hlam, p976_0]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h0, hlam, p976_0]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h636, hlam, p976_0]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h846, hlam, p976_0]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h928, hlam, p976_0]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h0, hc01, hlam, hphi, ht12, p976_1, u2elo1]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [hlam, p976_0]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h0, h934, h966, h974, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p976_1, u2elo1]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h0, h933, h966, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p976_1, u2elo1]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p976_1, u2elo1, u5ehi0]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h0, h930, hc01, hlam, hphi, ht12, p976_1, u2elo1]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h930, hlam, p976_0]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [hlam, p976_0]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h0, h930, h933, h966, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p976_1, u2elo1]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h0, h930, hlam, hphi, ht01, ht0b, ht12, ht5b, p976_1, u2elo1, u5ehi0]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h846, h964, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p976_1]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h931, hlam, p976_0]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h933, hlam, p976_1]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [hlam, p976_0]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h935, hlam, p976_1]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h0, h932, hc01, hlam, hphi, ht12, p976_1, u2elo1]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h932, hlam, p976_0]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h934, hlam, p976_0]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [h0, h846, h930, h934, hc01, hlam, hphi, ht12, p976_1, u2elo1]
                                          · have p976_0 := h976c.1
                                            have p976_1 := h976c.2.1
                                            have p976_2 := h976c.2.2.1
                                            have p976_3 := h976c.2.2.2
                                            linarith only [hlam, p976_0]
                              · linarith only [h636, h934, h963, hlam]
                            · linarith only [h636, h933, h934, h962, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                          · linarith only [h0, h930, h934, h961, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                        · linarith only [h0, h931, h960, hlam]
                      · linarith only [h0, h930, h934, h959, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1007 | h1007
                    · linarith only [h1007, h933, h934, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1009 | h1009
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1010 | h1010
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1011 | h1011
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1012 | h1012
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1013 | h1013
                              · linarith only [h1009, h1013, h933, h934, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1015 | h1015
                                · linarith only [h1007, h1010, h1015, h846, hc01, hlam, hphi, ht12, u2elo1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1017 | h1017
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1018 | h1018
                                    · linarith only [h1013, h1018, h930, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1020 | h1020
                                      · linarith only [h0, h1020, h931, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1022 | h1022
                                        · linarith only [h1015, h1022, h846, hc01, hc34, hlam, hphi, ht12, ht23]
                                        · rcases h0bigk with h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [hlam, p1024_0]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h0, hlam, p1024_0]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h636, hlam, p1024_0]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h846, hlam, p1024_0]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h928, hlam, p1024_0]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h0, hc01, hlam, hphi, ht12, p1024_1, u2elo1]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [hlam, p1024_0]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h0, h1017, h930, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1024_1, u2elo1]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h0, h846, hc01, hlam, hphi, ht12, p1024_1, u2elo1]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p1024_1, u2elo1, u5ehi0]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h1013, h636, hc01, hc35, hlam, hphi, ht12, ht23, p1024_1]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h930, hlam, p1024_0]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [hlam, p1024_0]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h1013, h1022, h636, h846, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1024_1]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h934, hlam, p1024_1]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h0, h931, hc01, hlam, hphi, ht12, p1024_1, u2elo1]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h931, hlam, p1024_0]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h933, hlam, p1024_1]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [hlam, p1024_0]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h1007, hlam, p1024_1]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h1011, h928, hc01, hlam, hphi, ht12, p1024_1, u2elo1]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h932, hlam, p1024_0]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h1011, h636, h928, hc01, hlam, hphi, ht12, p1024_1, u2elo1]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [h1011, h846, h928, hc01, hlam, hphi, ht12, p1024_1, u2elo1]
                                          · have p1024_0 := h1024c.1
                                            have p1024_1 := h1024c.2.1
                                            have p1024_2 := h1024c.2.2.1
                                            have p1024_3 := h1024c.2.2.2
                                            linarith only [hlam, p1024_0]
                                  · linarith only [h1013, h1017, h636, h933, hc23, hc35, hlam, hphi]
                            · linarith only [h0, h1012, h636, h931, h933, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h0, h1011, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h1010, h931, hlam]
                      · linarith only [h0, h1009, h932, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1055 | h1055
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1056 | h1056
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1057 | h1057
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1058 | h1058
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1059 | h1059
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1060 | h1060
                            · linarith only [h1055, h1060, h933, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1062 | h1062
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1063 | h1063
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1064 | h1064
                                  · linarith only [h1060, h1064, h930, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1066 | h1066
                                    · linarith only [h0, h1064, h1066, h931, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                    · linarith only [h1055, h1060, h1066, h636, hc23, hc34, hlam, hphi]
                                · linarith only [h1056, h1063, h846, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                              · linarith only [h0, h1055, h1062, h636, h931, h933, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h0, h1059, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h1058, h931, hlam]
                      · linarith only [h0, h1055, h1057, h931, h933, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                    · linarith only [h1055, h1056, h933, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1075 | h1075
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1076 | h1076
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1077 | h1077
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1078 | h1078
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1079 | h1079
                            · linarith only [h1075, h1076, h1079, h933, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1081 | h1081
                              · linarith only [h1055, h1077, h1079, h1081, h636, hc01, hlam, hphi, ht12, u2elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1083 | h1083
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1084 | h1084
                                  · linarith only [h1079, h1084, h636, hc01, hlam, hphi, ht12, u2elo2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1086 | h1086
                                    · linarith only [h1081, h1084, h1086, h636, h931, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1088 | h1088
                                      · linarith only [h0, h1088, h931, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1090 | h1090
                                        · rcases h0bigk with h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [hlam, p1091_0]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h0, hlam, p1091_0]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h636, hlam, p1091_0]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h846, hlam, p1091_0]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h928, hlam, p1091_0]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h0, hc01, hlam, hphi, ht12, p1091_1, u2elo1]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [hlam, p1091_0]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h0, h636, hc01, hlam, hphi, ht12, p1091_1, u2elo1]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h0, h1075, h1084, h1088, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1091_1, u2elo1]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p1091_1, u2elo1, u5ehi0]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h1081, h1090, h636, hc01, hc34, hlam, hphi, ht12, ht23, p1091_1]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h930, hlam, p1091_0]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [hlam, p1091_0]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h933, hlam, p1091_0]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h1055, hlam, p1091_1]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h1077, h846, hc01, hlam, hphi, ht12, p1091_1, u2elo1]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h931, hlam, p1091_0]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h1077, h636, h846, hc01, hlam, hphi, ht12, p1091_1, u2elo1]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [hlam, p1091_0]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h1077, h846, h932, hlam, hphi, ht01, ht0b, ht12, ht5b, p1091_1, u2elo1, u5ehi2]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h1077, h1083, h928, hc01, hlam, hphi, ht12, p1091_1, u2elo1]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h932, hlam, p1091_0]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h1077, h1083, h636, h928, hc01, hlam, hphi, ht12, p1091_1, u2elo1]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [h1075, hlam, p1091_0]
                                          · have p1091_0 := h1091c.1
                                            have p1091_1 := h1091c.2.1
                                            have p1091_2 := h1091c.2.2.1
                                            have p1091_3 := h1091c.2.2.2
                                            linarith only [hlam, p1091_0]
                                        · linarith only [h1075, h1077, h1090, h636, h846, h933, hc01, hlam, hphi, ht12, u2elo1]
                                · linarith only [h1075, h1083, h846, hlam]
                          · linarith only [h1075, h1077, h1078, h846, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                        · linarith only [h0, h1075, h1077, h931, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                      · linarith only [h0, h1075, h1076, h931, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1122 | h1122
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1123 | h1123
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1124 | h1124
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1125 | h1125
                            · linarith only [h1122, h1125, h636, h933, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1127 | h1127
                              · linarith only [h1055, h1125, h1127, h636, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1129 | h1129
                                · linarith only [h1075, h1123, h1129, h846, hc01, hlam, hphi, ht12, u2elo1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1131 | h1131
                                  · linarith only [h1131, h930, h933, hlam]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1133 | h1133
                                    · linarith only [h1127, h1133, h636, hc01, hlam, hphi, ht12, u2elo2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1135 | h1135
                                      · linarith only [h1129, h1135, h846, h931, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1137 | h1137
                                        · linarith only [h1125, h1129, h1137, h636, hc01, hc34, hlam, hphi, ht12, ht23]
                                        · linarith only [h1125, h1137, h636, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h0, h1124, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h1123, h932, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                      · linarith only [h0, h1122, h930, h932, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1143 | h1143
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1144 | h1144
                  · linarith only [h1144, h930, h932, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1146 | h1146
                    · linarith only [h1146, h931, h932, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1148 | h1148
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1149 | h1149
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1150 | h1150
                          · linarith only [h1150, h932, hc02, hlam, hphi, u2elo1]
                          · linarith only [h0, h1150, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h1148, h1149, h636, h931, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1148, h930, h932, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1155 | h1155
                  · linarith only [h1143, h1155, h931, h932, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1157 | h1157
                    · linarith only [h1157, h931, h932, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1159 | h1159
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1160 | h1160
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1161 | h1161
                          · linarith only [h1161, h932, hc02, hlam, hphi, u2elo1]
                          · linarith only [h0, h1161, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h1159, h1160, h636, h931, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1159, h930, h932, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1166 | h1166
              · linarith only [h1166, h931, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1168 | h1168
                · linarith only [h1168, h930, h931, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1170 | h1170
                  · linarith only [h1170, h930, h931, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1172 | h1172
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1173 | h1173
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1174 | h1174
                        · linarith only [h1174, h931, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h1174, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h1173, h930, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1178 | h1178
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1179 | h1179
                        · linarith only [h1179, h931, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h1179, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h1178, h930, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1183 | h1183
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1184 | h1184
              · linarith only [h1184, h930, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1186 | h1186
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1187 | h1187
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1188 | h1188
                    · linarith only [h1183, h1188, h930, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1190 | h1190
                      · linarith only [h1190, h930, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1190, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1193 | h1193
                    · linarith only [h1183, h1193, h930, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1195 | h1195
                      · linarith only [h1195, h930, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1195, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1183, h1186, h930, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1199 | h1199
              · linarith only [h1183, h1199, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1201 | h1201
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1202 | h1202
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1203 | h1203
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1204 | h1204
                      · linarith only [h1204, h930, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1204, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1207 | h1207
                      · linarith only [h0, h1207, h930, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1207, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1210 | h1210
                    · linarith only [h1201, h1202, h1210, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1212 | h1212
                      · linarith only [h0, h1212, h930, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1212, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1215 | h1215
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1216 | h1216
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1217 | h1217
                      · linarith only [h0, h1217, h930, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1217, hc01, hlam, hphi, ht12, u2elo2]
                    · linarith only [h1201, h1215, h1216, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1221 | h1221
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1222 | h1222
                      · linarith only [h0, h1222, h930, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1222, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1225 | h1225
                      · linarith only [h0, h1225, h930, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1225, hc01, hlam, hphi, ht12, u2elo2]

theorem n7l_sBT2_M_LR_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.2.1
  have h2bigk := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h9, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h0, h4, h7, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h3, h7, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
                  · linarith only [h0, h13, h2, h7, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15 | h15
                    · linarith only [h0, h15, h2, h7, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h17 | h17
                      · linarith only [h0, h13, h17, h3, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                          · linarith only [h0, h2, h20, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                          · linarith only [h0, h13, h19, h2, h20, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h0, h19, h2, h5, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
                · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
                    · linarith only [h0, h26, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h0, h25, h26, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h0, h24, h25, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
                  · linarith only [h0, h2, h24, h30, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
                    · linarith only [h0, h2, h24, h32, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                      · linarith only [h0, h3, h30, h34, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                          · linarith only [h0, h2, h37, h6, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h39 | h39
                            · linarith only [h0, h34, h36, h37, h39, h4, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h41 | h41
                              · linarith only [h0, h30, h36, h37, h39, h4, h41, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · rcases h2bigk with h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  rcases p43_3 (m.d 0 2) (by simp) with h45 | h45
                                  · rcases p43_3 (m.d 1 2) (by simp) with h46 | h46
                                    · linarith only [h0, h46, hlam]
                                    · rcases p43_3 (m.d 2 3) (by simp) with h48 | h48
                                      · linarith only [h2, h48, hlam]
                                      · linarith only [h24, h48, hlam]
                                  · linarith only [h0, h45, hlam]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h0, h36, h41, h5, h6, hc34, hc45, hlam, hphi, p43_1, u0ehi8, u0elo0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h0, h30, h41, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34, p43_1, u0ehi8, u0elo0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h0, h32, hlam, hphi, ht0b, ht5b, p43_1, u0elo0, u5ehi1]
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
                                  linarith only [h24, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h30, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h32, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h2, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h0, h2, h41, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34, p43_1, u0ehi8, u0elo0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h0, h2, h30, h41, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34, p43_1, u0ehi8, u0elo0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h37, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h3, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h0, h3, h41, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34, p43_1, u0ehi8, u0elo0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h36, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h39, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h4, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h0, h4, h41, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34, p43_1, u0ehi8, u0elo0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h0, h4, h41, h5, h6, hc23, hc45, hlam, hphi, ht34, p43_1, u0ehi8, u0elo0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h0, h30, h4, h41, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34, p43_1, u0ehi8, u0elo0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [hlam, p43_0]
                        · linarith only [h36, h5, h6, hc23, hc35, hlam, hphi]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h76 | h76
              · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
                · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
                    · linarith only [h0, h79, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h0, h4, h78, h79, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h0, h3, h77, h78, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h83 | h83
                  · linarith only [h0, h2, h77, h83, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h85 | h85
                    · linarith only [h0, h2, h77, h85, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h87 | h87
                      · linarith only [h0, h3, h83, h87, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h89 | h89
                        · linarith only [h0, h2, h5, h76, h89, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h91 | h91
                          · linarith only [h0, h3, h89, h91, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                          · linarith only [h76, h77, h91, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
                · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h96 | h96
                    · linarith only [h0, h96, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h0, h4, h94, h96, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h3, h94, h95, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
                  · linarith only [h0, h100, h2, h94, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h102 | h102
                    · linarith only [h0, h102, h2, h94, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
                      · linarith only [h0, h100, h104, h3, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                        · linarith only [h0, h106, h2, h5, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h108 | h108
                          · linarith only [h0, h106, h108, h3, h76, hlam, hphi, u0ehi7, u0elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h110 | h110
                            · linarith only [h0, h104, h110, h3, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h112 | h112
                              · linarith only [h106, h110, h112, h94, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h112, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h115 | h115
            · rcases m.htr 0 3 5 (by decide) (by decide) with h116 | h116
              · linarith only [h116, h2, h4, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
                · rcases m.htr 1 2 4 (by decide) (by decide) with h119 | h119
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h120 | h120
                    · linarith only [h120, h4, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h122 | h122
                      · linarith only [h1, h119, h120, h122, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                        · linarith only [h1, h118, h120, h124, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h115, h116, h124, hc23, hc35, hlam, hphi]
                  · linarith only [h119, h3, h4, hc12, hc25, hlam, hphi]
                · linarith only [h118, h2, h4, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h129 | h129
              · linarith only [h129, h2, h4, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h131 | h131
                · rcases m.htr 1 2 4 (by decide) (by decide) with h132 | h132
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h133 | h133
                    · linarith only [h0, h115, h133, h3, h4, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h135 | h135
                      · linarith only [h1, h132, h133, h135, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h137 | h137
                        · linarith only [h1, h115, h131, h133, h137, hlam, hphi, u0ehi7, u0elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h139 | h139
                          · linarith only [h1, h129, h132, h133, h137, h139, hlam, hphi, u0ehi7, u0elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h141 | h141
                            · linarith only [h1, h132, h133, h135, h141, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h143 | h143
                              · linarith only [h115, h141, h143, h3, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                              · linarith only [h115, h143, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                  · linarith only [h132, h3, h4, hc12, hc25, hlam, hphi]
                · linarith only [h131, h2, h4, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h148 | h148
          · rcases m.htr 0 3 4 (by decide) (by decide) with h149 | h149
            · linarith only [h149, h2, h3, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h151 | h151
              · rcases m.htr 1 2 3 (by decide) (by decide) with h152 | h152
                · rcases m.htr 1 2 4 (by decide) (by decide) with h153 | h153
                  · linarith only [h0, h151, h153, h2, h3, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h155 | h155
                    · linarith only [h0, h155, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h148, h152, h155, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                · linarith only [h152, h2, h3, hc12, hc24, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h159 | h159
                · rcases m.htr 1 2 4 (by decide) (by decide) with h160 | h160
                  · linarith only [h0, h160, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h162 | h162
                    · linarith only [h0, h162, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h148, h159, h162, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h159, h2, h3, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h166 | h166
            · linarith only [h166, h2, h3, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h168 | h168
              · linarith only [h148, h168, h2, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
                · rcases m.htr 1 2 4 (by decide) (by decide) with h171 | h171
                  · linarith only [h171, h3, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h173 | h173
                    · linarith only [h0, h148, h173, h2, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h176 | h176
                        · linarith only [h166, h176, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                          · linarith only [h1, h168, h170, h173, h178, hlam, hphi, u0ehi7, u0elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h180 | h180
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h181 | h181
                              · rcases h2bigk with h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h170, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p182_1, u0elo1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h148, h176, h180, hc23, hc34, hlam, hphi, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h3, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h148, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h0, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p182_1, u0elo0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h171, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h173, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h2, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h170, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h176, hlam, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h178, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h176, h2, hc34, hlam, hphi, ht01, ht12, ht23, p182_1, u0ehi7]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h170, h176, hc23, hc34, hlam, hphi, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  rcases p182_3 (m.d 0 2) (by simp) with h200 | h200
                                  · linarith only [h200, h3, hlam]
                                  · linarith only [h2, h200, hlam]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h148, h176, h2, hc34, hlam, hphi, ht01, ht12, ht23, p182_1, u0ehi7]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h2, hc25, hlam, hphi, ht01, ht12, p182_1, u0ehi7]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h170, h178, hc23, hc35, hlam, hphi, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  rcases p182_3 (m.d 0 2) (by simp) with h207 | h207
                                  · linarith only [h148, h207, hlam]
                                  · linarith only [h2, h207, hlam]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h180, hlam, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [hlam, p182_0]
                              · linarith only [h175, h176, h181, h2, h3, hc14, hlam, hphi, ht01, u0ehi7]
                            · linarith only [h1, h175, h180, h2, h3, hlam, hphi, u0ehi7, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h214 | h214
                        · linarith only [h0, h170, h214, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h216 | h216
                          · linarith only [h1, h170, h171, h175, h216, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h218 | h218
                            · linarith only [h170, h171, h175, h214, h218, hc23, hc34, hlam, hphi]
                            · linarith only [h2, h218, h3, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                · linarith only [h170, h2, h3, hc12, hc24, hlam, hphi]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h222 | h222
        · rcases m.htr 0 2 5 (by decide) (by decide) with h223 | h223
          · rcases m.htr 0 3 4 (by decide) (by decide) with h224 | h224
            · rcases m.htr 0 3 5 (by decide) (by decide) with h225 | h225
              · rcases m.htr 1 2 3 (by decide) (by decide) with h226 | h226
                · linarith only [h2, h223, h226, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h228 | h228
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h229 | h229
                    · linarith only [h0, h229, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h2, h223, h229, hc12, hc23, hlam, hphi]
                  · linarith only [h2, h222, h228, hc12, hc23, hlam, hphi]
              · linarith only [h2, h223, h225, hlam]
            · linarith only [h2, h222, h224, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h235 | h235
            · rcases m.htr 0 3 5 (by decide) (by decide) with h236 | h236
              · rcases m.htr 1 2 3 (by decide) (by decide) with h237 | h237
                · linarith only [h0, h2, h222, h237, hlam, hphi, u0ehi8, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h239 | h239
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h240 | h240
                    · linarith only [h0, h222, h223, h240, hlam, hphi, u0ehi8, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h242 | h242
                      · linarith only [h1, h239, h240, h242, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h245 | h245
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h246 | h246
                            · linarith only [h1, h239, h240, h242, h246, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h248 | h248
                              · linarith only [h1, h222, h223, h239, h240, h244, h246, h248, hlam, hphi, u0ehi8, u0elo0]
                              · rcases h2bigk with h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h223, h246, hc12, hc45, hlam, hphi, ht23, ht34, p250_1]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h2, hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h223, h244, h246, hc34, hc45, hlam, hphi, p250_1]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h223, hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h0, hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h237, hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h0, h222, h223, h244, h246, hc34, hc45, hlam, hphi, p250_1, u0ehi8, u0elo0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h240, hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h222, hc23, hlam, hphi, ht01, ht12, p250_1, u0ehi8]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  rcases p250_3 (m.d 0 2) (by simp) with h262 | h262
                                  · linarith only [h2, h262, hlam]
                                  · linarith only [h0, h262, hlam]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  rcases p250_3 (m.d 0 2) (by simp) with h266 | h266
                                  · linarith only [h2, h266, hlam]
                                  · linarith only [h222, h266, hlam]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h222, h223, hc23, hlam, hphi, ht01, ht12, p250_1, u0ehi8]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h222, hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h239, hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h244, hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h246, hlam, p250_0]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h222, h246, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p250_1, u0ehi8]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h239, h246, hc24, hc45, hlam, hphi, p250_1]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [h245, hlam, p250_1]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  rcases p250_3 (m.d 0 2) (by simp) with h278 | h278
                                  · linarith only [h223, h278, hlam]
                                  · linarith only [h222, h278, hlam]
                                · have p250_0 := h250c.1
                                  have p250_1 := h250c.2.1
                                  have p250_2 := h250c.2.2.1
                                  have p250_3 := h250c.2.2.2
                                  linarith only [hlam, p250_0]
                          · linarith only [h2, h222, h245, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                        · linarith only [h2, h222, h244, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                  · linarith only [h2, h222, h239, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h285 | h285
                · linarith only [h2, h285, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h287 | h287
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h288 | h288
                    · linarith only [h0, h288, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h290 | h290
                      · linarith only [h1, h287, h288, h290, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h292 | h292
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h293 | h293
                          · linarith only [h2, h222, h236, h293, hc23, hlam, hphi, ht01, ht12, u0ehi8]
                          · linarith only [h2, h222, h293, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                        · linarith only [h2, h222, h292, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                  · linarith only [h2, h222, h287, hc12, hc23, hlam, hphi]
            · linarith only [h2, h222, h235, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h299 | h299
          · rcases m.htr 0 3 4 (by decide) (by decide) with h300 | h300
            · rcases m.htr 0 3 5 (by decide) (by decide) with h301 | h301
              · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
                · linarith only [h2, h299, h302, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h304 | h304
                  · linarith only [h0, h222, h299, h304, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h306 | h306
                    · linarith only [h0, h306, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h2, h299, h306, hc12, hc23, hlam, hphi]
              · linarith only [h2, h299, h301, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h310 | h310
              · rcases m.htr 1 2 3 (by decide) (by decide) with h311 | h311
                · linarith only [h2, h299, h311, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h313 | h313
                  · linarith only [h0, h222, h299, h313, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h315 | h315
                    · linarith only [h0, h315, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · linarith only [h2, h299, h315, hc12, hc23, hlam, hphi]
              · linarith only [h2, h299, h310, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h319 | h319
            · rcases m.htr 0 3 5 (by decide) (by decide) with h320 | h320
              · rcases m.htr 1 2 3 (by decide) (by decide) with h321 | h321
                · linarith only [h2, h321, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h323 | h323
                  · linarith only [h0, h222, h323, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h325 | h325
                    · linarith only [h0, h299, h325, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h327 | h327
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h328 | h328
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h329 | h329
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h330 | h330
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h331 | h331
                              · linarith only [h319, h331, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                              · rcases h2bigk with h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [hlam, p333_0]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [h299, h328, h330, hc12, hc23, hlam, hphi, p333_1]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [h2, hlam, p333_0]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [h222, hlam, p333_0]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [h299, hlam, p333_0]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [h0, hlam, p333_0]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [hlam, p333_0]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [h321, hlam, p333_0]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [h323, hlam, p333_0]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [h325, hlam, p333_0]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p333_1, u0ehi6]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  rcases p333_3 (m.d 0 2) (by simp) with h345 | h345
                                  · linarith only [h2, h345, hlam]
                                  · linarith only [h0, h345, hlam]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [hlam, p333_0]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [h222, hc23, hlam, hphi, ht01, ht12, p333_1, u0ehi6]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [h299, hc23, hlam, hphi, ht01, ht12, p333_1, u0ehi6]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht12, p333_1, u0ehi6]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  rcases p333_3 (m.d 0 2) (by simp) with h352 | h352
                                  · linarith only [h222, h352, hlam]
                                  · linarith only [h0, h352, hlam]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [h328, hlam, p333_0]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [hlam, p333_0]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [h299, h328, hc23, hlam, hphi, ht01, ht12, p333_1, u0ehi6]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht12, p333_1, u0ehi6]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  rcases p333_3 (m.d 0 2) (by simp) with h359 | h359
                                  · linarith only [h299, h359, hlam]
                                  · linarith only [h0, h359, hlam]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [h329, hlam, p333_1]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [h330, hlam, p333_1]
                                · have p333_0 := h333c.1
                                  have p333_1 := h333c.2.1
                                  have p333_2 := h333c.2.2.1
                                  have p333_3 := h333c.2.2.2
                                  linarith only [hlam, p333_0]
                            · linarith only [h1, h222, h327, h330, hlam, hphi, u0ehi6, u0elo0]
                          · linarith only [h2, h329, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                        · linarith only [h2, h328, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h368 | h368
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h369 | h369
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h370 | h370
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h371 | h371
                              · linarith only [h319, h327, h371, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                              · rcases h2bigk with h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h299, h368, h370, hc12, hc23, hlam, hphi, p373_1]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h2, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h222, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h299, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h0, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h321, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h323, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h325, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p373_1, u0ehi6]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  rcases p373_3 (m.d 0 2) (by simp) with h385 | h385
                                  · linarith only [h2, h385, hlam]
                                  · linarith only [h0, h385, hlam]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h370, h371, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p373_1]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h299, hc23, hlam, hphi, ht01, ht12, p373_1, u0ehi6]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht12, p373_1, u0ehi6]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  rcases p373_3 (m.d 0 2) (by simp) with h392 | h392
                                  · linarith only [h222, h392, hlam]
                                  · linarith only [h0, h392, hlam]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h368, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h299, h368, hc23, hlam, hphi, ht01, ht12, p373_1, u0ehi6]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht12, p373_1, u0ehi6]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  rcases p373_3 (m.d 0 2) (by simp) with h399 | h399
                                  · linarith only [h299, h399, hlam]
                                  · linarith only [h0, h399, hlam]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h369, hlam, p373_1]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h370, hlam, p373_1]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hlam, p373_0]
                            · linarith only [h222, h370, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                          · linarith only [h2, h369, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                        · linarith only [h2, h368, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h408 | h408
                · linarith only [h2, h408, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h410 | h410
                  · linarith only [h0, h222, h410, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h412 | h412
                    · linarith only [h0, h412, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h414 | h414
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h415 | h415
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h416 | h416
                          · linarith only [h320, h416, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                          · linarith only [h2, h416, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                        · linarith only [h2, h319, h415, hlam, hphi, u0ehi6, u0elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h420 | h420
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h421 | h421
                          · linarith only [h320, h421, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                          · linarith only [h2, h421, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                        · linarith only [h2, h319, h420, hlam, hphi, u0ehi6, u0elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h425 | h425
              · rcases m.htr 1 2 3 (by decide) (by decide) with h426 | h426
                · linarith only [h2, h426, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h428 | h428
                  · linarith only [h0, h222, h428, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h430 | h430
                    · linarith only [h0, h299, h430, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h432 | h432
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h433 | h433
                        · linarith only [h319, h425, h433, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h2, h433, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h436 | h436
                        · linarith only [h299, h319, h425, h436, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                        · linarith only [h2, h436, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h439 | h439
                · linarith only [h2, h439, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h441 | h441
                  · linarith only [h0, h222, h441, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h443 | h443
                    · linarith only [h0, h299, h443, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h445 | h445
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h446 | h446
                        · linarith only [h319, h446, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                        · linarith only [h2, h446, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h449 | h449
                        · linarith only [h2, h319, h449, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                        · linarith only [h2, h449, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h452 | h452
      · rcases m.htr 0 2 4 (by decide) (by decide) with h453 | h453
        · rcases m.htr 0 2 5 (by decide) (by decide) with h454 | h454
          · linarith only [h0, h1, h454, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h456 | h456
            · rcases m.htr 0 3 5 (by decide) (by decide) with h457 | h457
              · linarith only [h0, h1, h452, h457, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h459 | h459
                · rcases m.htr 1 2 4 (by decide) (by decide) with h460 | h460
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h461 | h461
                    · linarith only [h0, h454, h461, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h463 | h463
                      · linarith only [h0, h1, h460, h461, h463, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h0, h1, h459, h463, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h453, h459, h460, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h452, h454, h459, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h468 | h468
              · linarith only [h0, h1, h452, h468, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h470 | h470
                · rcases m.htr 1 2 4 (by decide) (by decide) with h471 | h471
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h472 | h472
                    · linarith only [h0, h472, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h474 | h474
                      · linarith only [h0, h1, h471, h472, h474, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h0, h1, h470, h474, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h453, h470, h471, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h452, h454, h470, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h479 | h479
          · linarith only [h0, h1, h479, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h481 | h481
            · linarith only [h452, h453, h481, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h483 | h483
              · linarith only [h0, h1, h452, h483, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h485 | h485
                · rcases m.htr 1 2 4 (by decide) (by decide) with h486 | h486
                  · linarith only [h0, h1, h453, h486, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h488 | h488
                    · linarith only [h0, h1, h452, h479, h488, hlam, hphi, u0ehi7, u0elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h490 | h490
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h491 | h491
                        · linarith only [h0, h1, h481, h485, h486, h490, h491, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                        · linarith only [h0, h1, h485, h486, h490, h491, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h1, h485, h490, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h452, h453, h485, hc12, hc24, hlam, hphi]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h496 | h496
        · rcases m.htr 0 2 5 (by decide) (by decide) with h497 | h497
          · linarith only [h0, h1, h497, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h499 | h499
            · rcases m.htr 0 3 5 (by decide) (by decide) with h500 | h500
              · rcases m.htr 1 2 3 (by decide) (by decide) with h501 | h501
                · linarith only [h452, h501, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h503 | h503
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h504 | h504
                    · linarith only [h0, h1, h496, h497, h500, h504, hlam, hphi, u0ehi8, u0elo2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h506 | h506
                      · linarith only [h0, h1, h503, h504, h506, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h0, h1, h503, h506, hc24, hc45, hlam, hphi]
                  · linarith only [h452, h496, h503, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h510 | h510
                · linarith only [h0, h452, h510, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h512 | h512
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h513 | h513
                    · linarith only [h0, h1, h496, h497, h513, hc15, hlam, hphi, ht01, u0ehi8]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h515 | h515
                      · linarith only [h0, h1, h512, h513, h515, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h0, h1, h512, h515, hc24, hc45, hlam, hphi]
                  · linarith only [h452, h496, h512, hc12, hc23, hlam, hphi]
            · linarith only [h452, h496, h499, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h520 | h520
          · linarith only [h0, h1, h520, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h522 | h522
            · rcases m.htr 0 3 5 (by decide) (by decide) with h523 | h523
              · rcases m.htr 1 2 3 (by decide) (by decide) with h524 | h524
                · linarith only [h0, h452, h524, hlam, hphi, u0ehi6, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h526 | h526
                  · linarith only [h0, h1, h496, h523, h526, hlam, hphi, u0ehi6, u0elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h528 | h528
                    · linarith only [h0, h1, h520, h523, h528, hlam, hphi, u0ehi6, u0elo2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h530 | h530
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h531 | h531
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h532 | h532
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h533 | h533
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h534 | h534
                              · linarith only [h522, h534, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                              · rcases h2bigk with h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h0, h1, h526, h530, h531, hc12, hc23, hlam, hphi, p536_1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h452, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h496, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h520, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h0, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h524, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h526, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h528, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p536_1, u0ehi6]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  rcases p536_3 (m.d 0 2) (by simp) with h548 | h548
                                  · linarith only [h452, h548, hlam]
                                  · linarith only [h0, h548, hlam]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h1, h526, h530, hc01, hc23, hlam, hphi, ht12, p536_1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h0, h1, h528, hc23, hlam, hphi, ht01, ht12, p536_1, u0ehi6]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht12, p536_1, u0ehi6]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  rcases p536_3 (m.d 0 2) (by simp) with h555 | h555
                                  · linarith only [h496, h555, hlam]
                                  · linarith only [h0, h555, hlam]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h531, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h0, h1, h528, h531, hc23, hlam, hphi, ht01, ht12, p536_1, u0ehi6]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht12, p536_1, u0ehi6]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  rcases p536_3 (m.d 0 2) (by simp) with h562 | h562
                                  · linarith only [h520, h562, hlam]
                                  · linarith only [h0, h562, hlam]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h532, hlam, p536_1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h533, hlam, p536_1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hlam, p536_0]
                            · linarith only [h496, h533, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                          · linarith only [h452, h532, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                        · linarith only [h452, h531, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h571 | h571
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h572 | h572
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h573 | h573
                            · linarith only [h0, h1, h530, h573, hc24, hlam, hphi, ht01, ht12, u0ehi6]
                            · linarith only [h496, h573, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                          · linarith only [h452, h523, h572, hlam, hphi, u0ehi6, u0elo2]
                        · linarith only [h452, h522, h571, hlam, hphi, u0ehi6, u0elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h578 | h578
                · linarith only [h452, h578, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h580 | h580
                  · linarith only [h0, h496, h580, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h582 | h582
                    · linarith only [h0, h1, h582, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h584 | h584
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h585 | h585
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h586 | h586
                          · linarith only [h523, h586, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                          · linarith only [h0, h1, h580, h584, h585, h586, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h452, h522, h585, hlam, hphi, u0ehi6, u0elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h590 | h590
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h591 | h591
                          · linarith only [h523, h591, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                          · linarith only [h452, h591, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                        · linarith only [h452, h522, h590, hlam, hphi, u0ehi6, u0elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h595 | h595
              · rcases m.htr 1 2 3 (by decide) (by decide) with h596 | h596
                · linarith only [h452, h596, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h598 | h598
                  · linarith only [h0, h496, h598, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h600 | h600
                    · linarith only [h0, h1, h522, h595, h600, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h602 | h602
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h603 | h603
                        · linarith only [h0, h1, h522, h595, h603, hc12, hc23, hlam, hphi]
                        · linarith only [h452, h603, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h606 | h606
                        · linarith only [h0, h1, h522, h595, h606, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                        · linarith only [h452, h606, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h609 | h609
                · linarith only [h0, h452, h609, hlam, hphi, u0ehi6, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h611 | h611
                  · linarith only [h0, h1, h496, h611, hlam, hphi, u0ehi6, u0elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h613 | h613
                    · linarith only [h0, h1, h613, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h615 | h615
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h616 | h616
                        · linarith only [h452, h522, h616, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                        · linarith only [h452, h616, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h619 | h619
                        · linarith only [h452, h522, h619, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                        · linarith only [h452, h619, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h622 | h622
    · rcases m.htr 0 2 3 (by decide) (by decide) with h623 | h623
      · rcases m.htr 0 2 4 (by decide) (by decide) with h624 | h624
        · rcases m.htr 0 2 5 (by decide) (by decide) with h625 | h625
          · rcases m.htr 0 3 4 (by decide) (by decide) with h626 | h626
            · rcases m.htr 0 3 5 (by decide) (by decide) with h627 | h627
              · rcases m.htr 1 2 3 (by decide) (by decide) with h628 | h628
                · rcases m.htr 1 2 4 (by decide) (by decide) with h629 | h629
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h630 | h630
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h631 | h631
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h632 | h632
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h633 | h633
                          · linarith only [h623, h633, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                          · linarith only [h627, h632, h633, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h636 | h636
                          · linarith only [h623, h626, h632, h636, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h638 | h638
                            · linarith only [h624, h638, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h640 | h640
                              · linarith only [h623, h626, h632, h638, h640, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · linarith only [h0, h622, h631, h632, h640, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h643 | h643
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h644 | h644
                          · linarith only [h623, h644, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                          · linarith only [h623, h627, h643, h644, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h647 | h647
                          · linarith only [h623, h647, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h649 | h649
                            · linarith only [h0, h622, h629, h631, h649, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h651 | h651
                              · linarith only [h623, h626, h631, h651, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases h2bigk with h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h0, hlam, p653_1]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  rcases p653_3 (m.d 0 2) (by simp) with h656 | h656
                                  · rcases p653_3 (m.d 1 2) (by simp) with h657 | h657
                                    · rcases p653_3 (m.d 2 3) (by simp) with h658 | h658
                                      · linarith only [h658, hlam, p653_0]
                                      · rcases p653_3 (m.d 2 4) (by simp) with h660 | h660
                                        · linarith only [h624, h660, hlam]
                                        · linarith only [h643, h660, hlam]
                                    · linarith only [h628, h657, hlam]
                                  · linarith only [h656, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  rcases p653_3 (m.d 0 2) (by simp) with h665 | h665
                                  · rcases p653_3 (m.d 1 2) (by simp) with h666 | h666
                                    · rcases p653_3 (m.d 2 3) (by simp) with h667 | h667
                                      · linarith only [h623, h667, hlam]
                                      · rcases p653_3 (m.d 2 4) (by simp) with h669 | h669
                                        · linarith only [h669, hlam, p653_0]
                                        · rcases p653_3 (m.d 2 5) (by simp) with h671 | h671
                                          · linarith only [h625, h671, hlam]
                                          · linarith only [h649, h671, hlam]
                                    · linarith only [h629, h666, hlam]
                                  · linarith only [h665, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht5b, p653_1, u0elo1, u5ehi2]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h623, h627, h643, h651, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p653_1]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  rcases p653_3 (m.d 0 2) (by simp) with h679 | h679
                                  · linarith only [h0, h679, hlam]
                                  · linarith only [h623, h679, hlam]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  rcases p653_3 (m.d 0 2) (by simp) with h682 | h682
                                  · linarith only [h0, h682, hlam]
                                  · linarith only [h624, h682, hlam]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  rcases p653_3 (m.d 0 2) (by simp) with h685 | h685
                                  · linarith only [h0, h685, hlam]
                                  · linarith only [h625, h685, hlam]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h623, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h628, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h643, hlam, p653_1]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h647, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h624, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h629, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h624, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p653_1, u0elo1]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h649, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h625, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h630, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h625, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p653_1, u0elo1]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h622, h630, hc24, hlam, hphi, ht0b, ht45, ht5b, p653_1, u0elo0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [hlam, p653_0]
                    · linarith only [h0, h625, h630, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h622, h629, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h622, h628, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h706 | h706
                · rcases m.htr 1 2 4 (by decide) (by decide) with h707 | h707
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h708 | h708
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h709 | h709
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h710 | h710
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h711 | h711
                          · linarith only [h623, h626, h627, h711, hlam, hphi, u0ehi8, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h713 | h713
                            · linarith only [h622, h708, h710, h711, h713, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h715 | h715
                              · linarith only [h626, h627, h713, h715, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                              · linarith only [h622, h626, h627, h709, h715, hlam, hphi, u0ehi8, u0elo0]
                        · linarith only [h626, h627, h710, hc23, hc35, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h719 | h719
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h720 | h720
                          · linarith only [h623, h626, h627, h720, hlam, hphi, u0ehi8, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h722 | h722
                            · linarith only [h624, h722, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h724 | h724
                              · linarith only [h0, h622, h708, h709, h719, h720, h724, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases h2bigk with h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [hlam, p726_0]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [h0, hlam, p726_1]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [h626, h627, h719, h724, hc34, hc45, hlam, hphi, p726_1, u0ehi8, u0elo1]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  rcases p726_3 (m.d 0 2) (by simp) with h730 | h730
                                  · rcases p726_3 (m.d 1 2) (by simp) with h731 | h731
                                    · rcases p726_3 (m.d 2 3) (by simp) with h732 | h732
                                      · linarith only [h623, h732, hlam]
                                      · linarith only [h719, h732, hlam]
                                    · linarith only [h707, h731, hlam]
                                  · linarith only [h730, hlam, p726_0]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht5b, p726_1, u0elo1, u5ehi2]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht01, p726_1, u0ehi6]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [hlam, p726_0]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  rcases p726_3 (m.d 0 2) (by simp) with h740 | h740
                                  · linarith only [h0, h740, hlam]
                                  · linarith only [h623, h740, hlam]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  rcases p726_3 (m.d 0 2) (by simp) with h743 | h743
                                  · linarith only [h0, h743, hlam]
                                  · linarith only [h624, h743, hlam]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  rcases p726_3 (m.d 0 2) (by simp) with h746 | h746
                                  · linarith only [h0, h746, hlam]
                                  · linarith only [h625, h746, hlam]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [h623, hlam, p726_0]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [h706, hlam, p726_0]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [hlam, p726_0]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [h623, h626, h627, h724, hc24, hc45, hlam, hphi, p726_1, u0ehi8, u0elo1]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [h720, hlam, p726_0]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [h624, hlam, p726_0]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [h707, hlam, p726_0]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [h719, hlam, p726_0]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [hlam, p726_0]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [h722, hlam, p726_0]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [h625, hlam, p726_0]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [h708, hlam, p726_0]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [h625, h626, h627, h724, hc23, hc45, hlam, hphi, ht34, p726_1, u0ehi8, u0elo1]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [h0, h622, h626, h627, h708, h719, h724, hc12, hc34, hc45, hlam, hphi, ht01, p726_1, u0ehi8]
                                · have p726_0 := h726c.1
                                  have p726_1 := h726c.2.1
                                  have p726_2 := h726c.2.2.1
                                  have p726_3 := h726c.2.2.2
                                  linarith only [hlam, p726_0]
                        · linarith only [h626, h627, h719, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h622, h708, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h707, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h622, h626, h627, h706, hc23, hlam, hphi, ht01, ht12, u0ehi8]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h768 | h768
              · rcases m.htr 1 2 3 (by decide) (by decide) with h769 | h769
                · rcases m.htr 1 2 4 (by decide) (by decide) with h770 | h770
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h771 | h771
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h772 | h772
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h773 | h773
                        · linarith only [h623, h626, h773, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h775 | h775
                          · linarith only [h624, h773, h775, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                          · linarith only [h626, h768, h775, hc23, hc34, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h778 | h778
                        · linarith only [h626, h768, h778, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h780 | h780
                          · linarith only [h622, h770, h772, h778, h780, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                          · linarith only [h626, h768, h780, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h622, h771, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h622, h770, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h622, h769, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h786 | h786
                · rcases m.htr 1 2 4 (by decide) (by decide) with h787 | h787
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h788 | h788
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h789 | h789
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h790 | h790
                        · linarith only [h623, h626, h790, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h792 | h792
                          · linarith only [h624, h768, h790, h792, hlam, hphi, u0ehi7, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h794 | h794
                            · linarith only [h624, h794, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h796 | h796
                              · rcases h2bigk with h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h0, hlam, p797_1]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  rcases p797_3 (m.d 0 2) (by simp) with h800 | h800
                                  · rcases p797_3 (m.d 1 2) (by simp) with h801 | h801
                                    · rcases p797_3 (m.d 2 3) (by simp) with h802 | h802
                                      · linarith only [h802, hlam, p797_0]
                                      · rcases p797_3 (m.d 2 4) (by simp) with h804 | h804
                                        · linarith only [h624, h804, hlam]
                                        · linarith only [h790, h804, hlam]
                                    · linarith only [h786, h801, hlam]
                                  · linarith only [h800, hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  rcases p797_3 (m.d 0 2) (by simp) with h809 | h809
                                  · rcases p797_3 (m.d 1 2) (by simp) with h810 | h810
                                    · rcases p797_3 (m.d 2 3) (by simp) with h811 | h811
                                      · linarith only [h623, h811, hlam]
                                      · rcases p797_3 (m.d 2 4) (by simp) with h813 | h813
                                        · linarith only [h813, hlam, p797_0]
                                        · rcases p797_3 (m.d 2 5) (by simp) with h815 | h815
                                          · linarith only [h625, h815, hlam]
                                          · linarith only [h794, h815, hlam]
                                    · linarith only [h787, h810, hlam]
                                  · linarith only [h809, hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht5b, p797_1, u0elo1, u5ehi2]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht01, p797_1, u0ehi6]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h0, h622, h789, h790, h794, hlam, p797_2]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h0, h622, h789, h794, hlam, p797_2]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  rcases p797_3 (m.d 0 2) (by simp) with h825 | h825
                                  · linarith only [h0, h825, hlam]
                                  · linarith only [h625, h825, hlam]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h623, hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h786, hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h790, hlam, p797_1]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h792, hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h624, hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h787, hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h622, h789, h794, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p797_1, u0elo0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h794, hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h625, hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h788, hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h625, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p797_1, u0elo1]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h0, h622, h789, h794, hc24, hlam, hphi, ht0b, ht45, ht5b, p797_1, u0elo1]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [hlam, p797_0]
                              · linarith only [h0, h622, h626, h789, h796, hlam, hphi, u0ehi7, u0elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h844 | h844
                        · linarith only [h626, h786, h844, hc13, hlam, hphi, ht01, u0ehi7]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h846 | h846
                          · linarith only [h0, h622, h768, h787, h789, h844, h846, hlam, hphi, u0ehi7, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h848 | h848
                            · linarith only [h0, h622, h787, h789, h848, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h850 | h850
                              · rcases h2bigk with h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [hlam, p851_0]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [h0, hlam, p851_1]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  rcases p851_3 (m.d 0 2) (by simp) with h854 | h854
                                  · rcases p851_3 (m.d 1 2) (by simp) with h855 | h855
                                    · rcases p851_3 (m.d 2 3) (by simp) with h856 | h856
                                      · linarith only [h856, hlam, p851_0]
                                      · rcases p851_3 (m.d 2 4) (by simp) with h858 | h858
                                        · linarith only [h624, h858, hlam]
                                        · linarith only [h844, h858, hlam]
                                    · linarith only [h786, h855, hlam]
                                  · linarith only [h854, hlam, p851_0]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  rcases p851_3 (m.d 0 2) (by simp) with h863 | h863
                                  · rcases p851_3 (m.d 1 2) (by simp) with h864 | h864
                                    · rcases p851_3 (m.d 2 3) (by simp) with h865 | h865
                                      · linarith only [h623, h865, hlam]
                                      · rcases p851_3 (m.d 2 4) (by simp) with h867 | h867
                                        · linarith only [h867, hlam, p851_0]
                                        · rcases p851_3 (m.d 2 5) (by simp) with h869 | h869
                                          · linarith only [h625, h869, hlam]
                                          · linarith only [h848, h869, hlam]
                                    · linarith only [h787, h864, hlam]
                                  · linarith only [h863, hlam, p851_0]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht5b, p851_1, u0elo1, u5ehi2]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [h0, h622, hc12, hlam, hphi, ht01, ht0b, ht5b, p851_1, u5ehi1]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [hlam, p851_0]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  rcases p851_3 (m.d 0 2) (by simp) with h877 | h877
                                  · linarith only [h0, h877, hlam]
                                  · linarith only [h623, h877, hlam]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  rcases p851_3 (m.d 0 2) (by simp) with h880 | h880
                                  · linarith only [h0, h880, hlam]
                                  · linarith only [h624, h880, hlam]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  rcases p851_3 (m.d 0 2) (by simp) with h883 | h883
                                  · linarith only [h0, h883, hlam]
                                  · linarith only [h625, h883, hlam]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [h623, hlam, p851_0]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [h786, hlam, p851_0]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [hlam, p851_0]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [h844, hlam, p851_1]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [h846, hlam, p851_0]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [h624, hlam, p851_0]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [h787, hlam, p851_0]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [h624, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p851_1, u0elo1]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [hlam, p851_0]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [h848, hlam, p851_0]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [h625, hlam, p851_0]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [h788, hlam, p851_0]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [h622, h788, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p851_1, u0elo0]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [h0, h622, h788, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p851_1]
                                · have p851_0 := h851c.1
                                  have p851_1 := h851c.2.1
                                  have p851_2 := h851c.2.2.1
                                  have p851_3 := h851c.2.2.2
                                  linarith only [hlam, p851_0]
                              · linarith only [h626, h850, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                    · linarith only [h0, h622, h788, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h622, h768, h787, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                · linarith only [h0, h622, h768, h786, hc23, hlam, hphi, ht01, ht12, u0ehi7]
          · linarith only [h0, h622, h625, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h906 | h906
          · rcases m.htr 0 3 4 (by decide) (by decide) with h907 | h907
            · linarith only [h623, h624, h907, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h909 | h909
              · rcases m.htr 1 2 3 (by decide) (by decide) with h910 | h910
                · rcases m.htr 1 2 4 (by decide) (by decide) with h911 | h911
                  · linarith only [h624, h906, h911, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h911, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h622, h623, h910, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h915 | h915
                · rcases m.htr 1 2 4 (by decide) (by decide) with h916 | h916
                  · linarith only [h624, h906, h916, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h622, h909, h916, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                · linarith only [h0, h622, h623, h909, h915, hlam, hphi, u0ehi7, u0elo1]
          · linarith only [h0, h622, h906, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h921 | h921
        · rcases m.htr 0 2 5 (by decide) (by decide) with h922 | h922
          · rcases m.htr 0 3 4 (by decide) (by decide) with h923 | h923
            · rcases m.htr 0 3 5 (by decide) (by decide) with h924 | h924
              · rcases m.htr 1 2 3 (by decide) (by decide) with h925 | h925
                · linarith only [h623, h922, h925, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h622, h925, hc23, hlam, hphi, ht01, ht12, u0ehi9]
              · linarith only [h0, h622, h623, h924, hlam]
            · linarith only [h623, h921, h923, hlam]
          · linarith only [h0, h622, h922, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h931 | h931
          · rcases m.htr 0 3 4 (by decide) (by decide) with h932 | h932
            · rcases m.htr 0 3 5 (by decide) (by decide) with h933 | h933
              · rcases m.htr 1 2 3 (by decide) (by decide) with h934 | h934
                · linarith only [h0, h622, h623, h934, hc12, hlam, hphi, ht01, u0ehi9]
                · linarith only [h0, h622, h934, hc23, hlam, hphi, ht01, ht12, u0ehi9]
              · linarith only [h0, h622, h921, h932, h933, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h938 | h938
              · rcases m.htr 1 2 3 (by decide) (by decide) with h939 | h939
                · linarith only [h0, h622, h623, h939, hc12, hlam, hphi, ht01, u0ehi9]
                · linarith only [h0, h622, h939, hc23, hlam, hphi, ht01, ht12, u0ehi9]
              · linarith only [h0, h622, h623, h938, hlam]
          · linarith only [h0, h622, h931, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h944 | h944
      · rcases m.htr 0 2 4 (by decide) (by decide) with h945 | h945
        · rcases m.htr 0 2 5 (by decide) (by decide) with h946 | h946
          · rcases m.htr 0 3 4 (by decide) (by decide) with h947 | h947
            · rcases m.htr 0 3 5 (by decide) (by decide) with h948 | h948
              · rcases m.htr 1 2 3 (by decide) (by decide) with h949 | h949
                · rcases m.htr 1 2 4 (by decide) (by decide) with h950 | h950
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h951 | h951
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h952 | h952
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h953 | h953
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h954 | h954
                          · linarith only [h944, h954, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                          · linarith only [h948, h953, h954, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h957 | h957
                          · linarith only [h944, h957, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h959 | h959
                            · linarith only [h944, h947, h953, h959, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h961 | h961
                              · linarith only [h944, h947, h959, h961, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases h2bigk with h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [hlam, p963_0]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [h0, hlam, p963_1]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  rcases p963_3 (m.d 0 2) (by simp) with h966 | h966
                                  · rcases p963_3 (m.d 1 2) (by simp) with h967 | h967
                                    · rcases p963_3 (m.d 2 3) (by simp) with h968 | h968
                                      · linarith only [h968, hlam, p963_0]
                                      · rcases p963_3 (m.d 2 4) (by simp) with h970 | h970
                                        · linarith only [h945, h970, hlam]
                                        · linarith only [h953, h970, hlam]
                                    · linarith only [h949, h967, hlam]
                                  · linarith only [h966, hlam, p963_0]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  rcases p963_3 (m.d 0 2) (by simp) with h975 | h975
                                  · rcases p963_3 (m.d 1 2) (by simp) with h976 | h976
                                    · rcases p963_3 (m.d 2 3) (by simp) with h977 | h977
                                      · linarith only [h944, h977, hlam]
                                      · rcases p963_3 (m.d 2 4) (by simp) with h979 | h979
                                        · linarith only [h979, hlam, p963_0]
                                        · rcases p963_3 (m.d 2 5) (by simp) with h981 | h981
                                          · linarith only [h946, h981, hlam]
                                          · linarith only [h959, h981, hlam]
                                    · linarith only [h950, h976, hlam]
                                  · linarith only [h975, hlam, p963_0]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht5b, p963_1, u0elo1, u5ehi2]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [h944, h948, hc12, hlam, hphi, ht01, ht0b, ht5b, p963_1, u5ehi3]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [hlam, p963_0]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [h950, h952, h953, h961, hlam, p963_2]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  rcases p963_3 (m.d 0 2) (by simp) with h990 | h990
                                  · linarith only [h0, h990, hlam]
                                  · linarith only [h945, h990, hlam]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  rcases p963_3 (m.d 0 2) (by simp) with h993 | h993
                                  · linarith only [h0, h993, hlam]
                                  · linarith only [h946, h993, hlam]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [h944, hlam, p963_0]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [h949, hlam, p963_0]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [hlam, p963_0]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [h953, hlam, p963_1]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [h957, hlam, p963_0]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [h945, hlam, p963_0]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [h950, hlam, p963_0]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [h945, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p963_1, u0elo1]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [hlam, p963_0]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [h959, hlam, p963_0]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [h946, hlam, p963_0]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [h951, hlam, p963_0]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [h946, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p963_1, u0elo1]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [h948, h957, hc24, hlam, hphi, ht0b, ht45, ht5b, p963_1, u0elo2]
                                · have p963_0 := h963c.1
                                  have p963_1 := h963c.2.1
                                  have p963_2 := h963c.2.2.1
                                  have p963_3 := h963c.2.2.2
                                  linarith only [hlam, p963_0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1011 | h1011
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1012 | h1012
                          · linarith only [h1012, h944, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                          · linarith only [h1011, h1012, h944, h948, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1015 | h1015
                          · linarith only [h1015, h944, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1017 | h1017
                            · linarith only [h1011, h1017, h944, h947, h952, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1019 | h1019
                              · linarith only [h1019, h622, h944, h947, h952, hlam, hphi, u0ehi5, u0elo1]
                              · rcases h2bigk with h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [hlam, p1021_0]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [h0, hlam, p1021_1]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  rcases p1021_3 (m.d 0 2) (by simp) with h1024 | h1024
                                  · rcases p1021_3 (m.d 1 2) (by simp) with h1025 | h1025
                                    · rcases p1021_3 (m.d 2 3) (by simp) with h1026 | h1026
                                      · linarith only [h1026, hlam, p1021_0]
                                      · rcases p1021_3 (m.d 2 4) (by simp) with h1028 | h1028
                                        · linarith only [h1028, h945, hlam]
                                        · linarith only [h1011, h1028, hlam]
                                    · linarith only [h1025, h949, hlam]
                                  · linarith only [h1024, hlam, p1021_0]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  rcases p1021_3 (m.d 0 2) (by simp) with h1033 | h1033
                                  · rcases p1021_3 (m.d 1 2) (by simp) with h1034 | h1034
                                    · rcases p1021_3 (m.d 2 3) (by simp) with h1035 | h1035
                                      · linarith only [h1035, h944, hlam]
                                      · rcases p1021_3 (m.d 2 4) (by simp) with h1037 | h1037
                                        · linarith only [h1037, hlam, p1021_0]
                                        · rcases p1021_3 (m.d 2 5) (by simp) with h1039 | h1039
                                          · linarith only [h1039, h946, hlam]
                                          · linarith only [h1017, h1039, hlam]
                                    · linarith only [h1034, h950, hlam]
                                  · linarith only [h1033, hlam, p1021_0]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht5b, p1021_1, u0elo1, u5ehi2]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [h944, h948, hc12, hlam, hphi, ht01, ht0b, ht5b, p1021_1, u5ehi3]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [hlam, p1021_0]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  rcases p1021_3 (m.d 0 2) (by simp) with h1047 | h1047
                                  · linarith only [h0, h1047, hlam]
                                  · linarith only [h1047, h944, hlam]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  rcases p1021_3 (m.d 0 2) (by simp) with h1050 | h1050
                                  · linarith only [h0, h1050, hlam]
                                  · linarith only [h1050, h945, hlam]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  rcases p1021_3 (m.d 0 2) (by simp) with h1053 | h1053
                                  · linarith only [h0, h1053, hlam]
                                  · linarith only [h1053, h946, hlam]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [h944, hlam, p1021_0]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [h949, hlam, p1021_0]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [hlam, p1021_0]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [h1011, hlam, p1021_1]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [h1015, hlam, p1021_0]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [h945, hlam, p1021_0]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [h950, hlam, p1021_0]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [h945, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1021_1, u0elo1]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [hlam, p1021_0]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [h1017, hlam, p1021_0]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [h946, hlam, p1021_0]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [h951, hlam, p1021_0]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [h946, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1021_1, u0elo1]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [h1015, h948, hc24, hlam, hphi, ht0b, ht45, ht5b, p1021_1, u0elo2]
                                · have p1021_0 := h1021c.1
                                  have p1021_1 := h1021c.2.1
                                  have p1021_2 := h1021c.2.2.1
                                  have p1021_3 := h1021c.2.2.2
                                  linarith only [hlam, p1021_0]
                    · linarith only [h0, h946, h951, hlam, hphi, u0ehi5, u0elo1]
                  · linarith only [h0, h950, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h949, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1074 | h1074
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1075 | h1075
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1076 | h1076
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1077 | h1077
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1078 | h1078
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1079 | h1079
                          · linarith only [h1079, h944, h948, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1081 | h1081
                            · linarith only [h1078, h1079, h1081, h946, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1083 | h1083
                              · linarith only [h1078, h1079, h1081, h1083, h946, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h1075, h1077, h1083, h947, h948, hc12, hlam, hphi, ht01, u0ehi8]
                        · linarith only [h1078, h947, h948, hc23, hc35, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1087 | h1087
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1088 | h1088
                          · linarith only [h1088, h944, h947, h948, hlam, hphi, u0ehi8, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1090 | h1090
                            · linarith only [h1077, h1090, h945, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1092 | h1092
                              · linarith only [h1075, h1077, h1087, h1092, h622, hc14, hlam, hphi, ht01, u0ehi5]
                              · rcases h2bigk with h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [hlam, p1094_0]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [h0, hlam, p1094_1]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [h1087, h1092, h947, h948, hc34, hc45, hlam, hphi, p1094_1, u0ehi8, u0elo1]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  rcases p1094_3 (m.d 0 2) (by simp) with h1098 | h1098
                                  · rcases p1094_3 (m.d 1 2) (by simp) with h1099 | h1099
                                    · rcases p1094_3 (m.d 2 3) (by simp) with h1100 | h1100
                                      · linarith only [h1100, h944, hlam]
                                      · linarith only [h1087, h1100, hlam]
                                    · linarith only [h1075, h1099, hlam]
                                  · linarith only [h1098, hlam, p1094_0]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht5b, p1094_1, u0elo1, u5ehi2]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht01, p1094_1, u0ehi6]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [hlam, p1094_0]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  rcases p1094_3 (m.d 0 2) (by simp) with h1108 | h1108
                                  · linarith only [h0, h1108, hlam]
                                  · linarith only [h1108, h944, hlam]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  rcases p1094_3 (m.d 0 2) (by simp) with h1111 | h1111
                                  · linarith only [h0, h1111, hlam]
                                  · linarith only [h1111, h945, hlam]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  rcases p1094_3 (m.d 0 2) (by simp) with h1114 | h1114
                                  · linarith only [h0, h1114, hlam]
                                  · linarith only [h1114, h946, hlam]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [h944, hlam, p1094_0]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [h1074, hlam, p1094_0]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [hlam, p1094_0]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [h1088, h1092, h946, h947, h948, hc24, hc45, hlam, hphi, p1094_1, u0ehi8, u0elo1]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [h1088, hlam, p1094_0]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [h945, hlam, p1094_0]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [h1075, hlam, p1094_0]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [h1087, hlam, p1094_0]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [hlam, p1094_0]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [h1090, hlam, p1094_0]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [h946, hlam, p1094_0]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [h1076, hlam, p1094_0]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [h1092, h946, h947, h948, hc23, hc45, hlam, hphi, ht34, p1094_1, u0ehi8, u0elo1]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [h1087, h1092, h946, h947, h948, hc34, hc45, hlam, hphi, p1094_1, u0ehi8, u0elo1]
                                · have p1094_0 := h1094c.1
                                  have p1094_1 := h1094c.2.1
                                  have p1094_2 := h1094c.2.2.1
                                  have p1094_3 := h1094c.2.2.2
                                  linarith only [hlam, p1094_0]
                        · linarith only [h1087, h947, h948, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h1076, h946, hlam, hphi, u0ehi5, u0elo1]
                  · linarith only [h0, h1075, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h1074, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1136 | h1136
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1137 | h1137
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1138 | h1138
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1139 | h1139
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1140 | h1140
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1141 | h1141
                        · linarith only [h1141, h944, h947, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1143 | h1143
                          · linarith only [h1141, h1143, h945, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                          · linarith only [h1136, h1143, h947, hc23, hc34, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1146 | h1146
                        · linarith only [h1136, h1146, h947, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1148 | h1148
                          · linarith only [h1146, h1148, h945, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                          · linarith only [h1136, h1148, h947, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h1139, h946, hlam, hphi, u0ehi5, u0elo1]
                  · linarith only [h0, h1138, h945, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h0, h1137, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1154 | h1154
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1155 | h1155
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1156 | h1156
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1157 | h1157
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1158 | h1158
                        · linarith only [h1158, h944, h947, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1160 | h1160
                          · linarith only [h1136, h1158, h1160, h945, hlam, hphi, u0ehi7, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1162 | h1162
                            · linarith only [h1162, h945, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1164 | h1164
                              · rcases h2bigk with h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h0, hlam, p1165_1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  rcases p1165_3 (m.d 0 2) (by simp) with h1168 | h1168
                                  · rcases p1165_3 (m.d 1 2) (by simp) with h1169 | h1169
                                    · rcases p1165_3 (m.d 2 3) (by simp) with h1170 | h1170
                                      · linarith only [h1170, hlam, p1165_0]
                                      · rcases p1165_3 (m.d 2 4) (by simp) with h1172 | h1172
                                        · linarith only [h1172, h945, hlam]
                                        · linarith only [h1158, h1172, hlam]
                                    · linarith only [h1154, h1169, hlam]
                                  · linarith only [h1168, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  rcases p1165_3 (m.d 0 2) (by simp) with h1177 | h1177
                                  · rcases p1165_3 (m.d 1 2) (by simp) with h1178 | h1178
                                    · rcases p1165_3 (m.d 2 3) (by simp) with h1179 | h1179
                                      · linarith only [h1179, h944, hlam]
                                      · rcases p1165_3 (m.d 2 4) (by simp) with h1181 | h1181
                                        · linarith only [h1181, hlam, p1165_0]
                                        · rcases p1165_3 (m.d 2 5) (by simp) with h1183 | h1183
                                          · linarith only [h1183, h946, hlam]
                                          · linarith only [h1162, h1183, hlam]
                                    · linarith only [h1155, h1178, hlam]
                                  · linarith only [h1177, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht5b, p1165_1, u0elo1, u5ehi2]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht01, p1165_1, u0ehi6]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  rcases p1165_3 (m.d 0 2) (by simp) with h1191 | h1191
                                  · linarith only [h0, h1191, hlam]
                                  · linarith only [h1191, h944, hlam]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  rcases p1165_3 (m.d 0 2) (by simp) with h1194 | h1194
                                  · linarith only [h0, h1194, hlam]
                                  · linarith only [h1194, h945, hlam]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  rcases p1165_3 (m.d 0 2) (by simp) with h1197 | h1197
                                  · linarith only [h0, h1197, hlam]
                                  · linarith only [h1197, h946, hlam]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h944, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1154, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1158, hlam, p1165_1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1160, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h945, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1155, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h945, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1165_1, u0elo1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1162, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h946, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1156, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h946, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1165_1, u0elo1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h946, hc24, hlam, hphi, ht0b, ht45, ht5b, p1165_1, u0elo1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [hlam, p1165_0]
                              · linarith only [h1155, h1157, h1164, h947, hc12, hlam, hphi, ht01, u0ehi7]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1216 | h1216
                        · linarith only [h1216, h947, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1218 | h1218
                          · linarith only [h1136, h1216, h1218, h945, hlam, hphi, u0ehi7, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1220 | h1220
                            · linarith only [h1157, h1220, h945, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1222 | h1222
                              · linarith only [h1157, h1222, h622, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                              · linarith only [h1222, h947, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                    · linarith only [h0, h1156, h946, hlam, hphi, u0ehi5, u0elo1]
                  · linarith only [h0, h1155, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h1154, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1228 | h1228
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1229 | h1229
              · linarith only [h1229, h944, h946, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1231 | h1231
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1232 | h1232
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1233 | h1233
                    · linarith only [h1233, h946, hc12, hlam, hphi, ht01, u0ehi6]
                    · linarith only [h0, h1233, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h1232, h945, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h0, h1231, h944, h946, hc25, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1238 | h1238
              · linarith only [h1238, h944, h946, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1240 | h1240
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1241 | h1241
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1242 | h1242
                    · linarith only [h1228, h1242, h945, h946, hc12, hlam, hphi, ht01, u0ehi7]
                    · linarith only [h0, h1242, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h1241, h945, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h0, h1240, h944, h946, hc25, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1247 | h1247
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1248 | h1248
            · linarith only [h1248, h944, h945, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1250 | h1250
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1251 | h1251
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1252 | h1252
                  · linarith only [h1247, h1252, h945, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h1252, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h1251, h944, hlam, hphi, u0ehi5, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1256 | h1256
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1257 | h1257
                  · linarith only [h1247, h1257, h945, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h1257, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h1256, h944, hlam, hphi, u0ehi5, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1261 | h1261
            · linarith only [h1261, h944, h945, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1263 | h1263
              · linarith only [h1247, h1263, h944, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1265 | h1265
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1266 | h1266
                  · linarith only [h1266, h945, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h1266, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h1265, h944, hlam, hphi, u0ehi5, u0elo1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1270 | h1270
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1271 | h1271
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1272 | h1272
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1273 | h1273
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1274 | h1274
                · linarith only [h1271, h1274, h944, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h1274, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h1271, h1273, h944, hlam]
            · linarith only [h1270, h1272, h944, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1279 | h1279
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1280 | h1280
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1281 | h1281
                · linarith only [h1281, h944, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h1281, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1284 | h1284
                · linarith only [h1270, h1284, h944, hc12, hlam, hphi, ht01, u0ehi8]
                · linarith only [h0, h1284, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h1270, h1279, h944, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1288 | h1288
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1289 | h1289
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1290 | h1290
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1291 | h1291
                · linarith only [h1288, h1291, h622, h944, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h1291, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h1270, h1288, h1289, h1290, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1295 | h1295
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1296 | h1296
                · linarith only [h1288, h1296, h622, h944, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h1296, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h1288, h1295, h944, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1300 | h1300
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1301 | h1301
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1302 | h1302
                · linarith only [h0, h1302, h944, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h1302, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1305 | h1305
                · linarith only [h0, h1305, h944, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h1305, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1308 | h1308
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1309 | h1309
                · linarith only [h0, h1309, h944, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h1309, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1312 | h1312
                · linarith only [h0, h1312, h944, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h1312, hc23, hlam, hphi, ht01, ht12, u0ehi5]

end R2N4
