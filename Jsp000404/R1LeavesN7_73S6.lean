import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
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
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h14, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h0, h12, h13, h14, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                              · linarith only [h0, h13, h17, h2, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                                · linarith only [h0, h19, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                                  · linarith only [h0, h11, h19, h21, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases h2bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [hlam, p23_0]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht5b, p23_1, u5ehi2]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [h13, h2, h21, h5, h7, hlam, p23_2]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      rcases p23_3 (m.d 0 2) (by simp) with h27 | h27
                                      · rcases p23_3 (m.d 1 2) (by simp) with h28 | h28
                                        · linarith only [h0, h28, hlam]
                                        · linarith only [h28, h9, hlam]
                                      · linarith only [h27, hlam, p23_0]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      rcases p23_3 (m.d 0 2) (by simp) with h32 | h32
                                      · rcases p23_3 (m.d 1 2) (by simp) with h33 | h33
                                        · linarith only [h0, h33, hlam]
                                        · linarith only [h10, h33, hlam]
                                      · linarith only [h32, hlam, p23_0]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [h0, hlam, p23_0]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [hlam, p23_0]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      rcases p23_3 (m.d 0 2) (by simp) with h39 | h39
                                      · rcases p23_3 (m.d 1 2) (by simp) with h40 | h40
                                        · rcases p23_3 (m.d 2 3) (by simp) with h41 | h41
                                          · linarith only [h41, hlam, p23_0]
                                          · rcases p23_3 (m.d 2 4) (by simp) with h43 | h43
                                            · linarith only [h43, h9, hlam]
                                            · linarith only [h13, h43, hlam]
                                        · linarith only [h40, hlam, p23_0]
                                      · linarith only [h2, h39, hlam]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      rcases p23_3 (m.d 0 2) (by simp) with h48 | h48
                                      · rcases p23_3 (m.d 1 2) (by simp) with h49 | h49
                                        · rcases p23_3 (m.d 2 3) (by simp) with h50 | h50
                                          · linarith only [h50, h8, hlam]
                                          · rcases p23_3 (m.d 2 4) (by simp) with h52 | h52
                                            · linarith only [h52, hlam, p23_0]
                                            · rcases p23_3 (m.d 2 5) (by simp) with h54 | h54
                                              · linarith only [h10, h54, hlam]
                                              · linarith only [h19, h54, hlam]
                                        · linarith only [h49, hlam, p23_0]
                                      · linarith only [h3, h48, hlam]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p23_1, u5ehi2]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [h2, hlam, p23_0]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [h8, hlam, p23_0]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [hlam, p23_0]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [h13, hlam, p23_0]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [h17, hlam, p23_0]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [h3, hlam, p23_0]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [h9, hlam, p23_0]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p23_1]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [hlam, p23_0]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [h19, hlam, p23_1]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [h4, hlam, p23_0]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [h10, hlam, p23_0]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p23_1]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [h1, h12, h17, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                                    · have p23_0 := h23c.1
                                      have p23_1 := h23c.2.1
                                      have p23_2 := h23c.2.2.1
                                      have p23_3 := h23c.2.2.2
                                      linarith only [hlam, p23_0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h75 | h75
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h76 | h76
                              · linarith only [h0, h12, h76, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h78 | h78
                                · linarith only [h0, h78, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h80 | h80
                                  · linarith only [h12, h75, h78, h8, h80, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                  · rcases h2bigk with h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht5b, p82_1, u5ehi2]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      rcases p82_3 (m.d 0 2) (by simp) with h85 | h85
                                      · rcases p82_3 (m.d 1 2) (by simp) with h86 | h86
                                        · linarith only [h0, h86, hlam]
                                        · linarith only [h8, h86, hlam]
                                      · linarith only [h85, hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      rcases p82_3 (m.d 0 2) (by simp) with h90 | h90
                                      · rcases p82_3 (m.d 1 2) (by simp) with h91 | h91
                                        · linarith only [h0, h91, hlam]
                                        · linarith only [h9, h91, hlam]
                                      · linarith only [h90, hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      rcases p82_3 (m.d 0 2) (by simp) with h95 | h95
                                      · rcases p82_3 (m.d 1 2) (by simp) with h96 | h96
                                        · linarith only [h0, h96, hlam]
                                        · linarith only [h10, h96, hlam]
                                      · linarith only [h95, hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h0, hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h0, h75, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p82_1]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      rcases p82_3 (m.d 0 2) (by simp) with h103 | h103
                                      · rcases p82_3 (m.d 1 2) (by simp) with h104 | h104
                                        · rcases p82_3 (m.d 2 3) (by simp) with h105 | h105
                                          · linarith only [h105, h8, hlam]
                                          · linarith only [h105, h75, hlam]
                                        · linarith only [h104, hlam, p82_0]
                                      · linarith only [h103, h3, hlam]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h0, h75, h76, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p82_1]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h2, hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h8, hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h0, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p82_1]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h76, hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h3, hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h9, hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h75, hlam, p82_1]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h78, hlam, p82_1]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h4, hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h10, hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p82_1]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h0, h10, h75, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p82_1]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [hlam, p82_0]
                            · linarith only [h11, h12, h75, hc23, hc35, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h127 | h127
                          · linarith only [h0, h11, h127, h2, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h129 | h129
                            · linarith only [h0, h11, h129, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h131 | h131
                              · linarith only [h127, h131, h8, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h133 | h133
                                · linarith only [h0, h133, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h135 | h135
                                  · rcases h2bigk with h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [hlam, p136_0]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht5b, p136_1, u5ehi2]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [h129, h133, h135, h2, h5, hlam, p136_2]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [h133, h135, h2, h5, hlam, p136_2]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      rcases p136_3 (m.d 0 2) (by simp) with h141 | h141
                                      · rcases p136_3 (m.d 1 2) (by simp) with h142 | h142
                                        · linarith only [h0, h142, hlam]
                                        · linarith only [h10, h142, hlam]
                                      · linarith only [h141, hlam, p136_0]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [h0, hlam, p136_0]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [hlam, p136_0]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      rcases p136_3 (m.d 0 2) (by simp) with h148 | h148
                                      · rcases p136_3 (m.d 1 2) (by simp) with h149 | h149
                                        · rcases p136_3 (m.d 2 3) (by simp) with h150 | h150
                                          · linarith only [h150, hlam, p136_0]
                                          · rcases p136_3 (m.d 2 4) (by simp) with h152 | h152
                                            · linarith only [h152, h9, hlam]
                                            · linarith only [h129, h152, hlam]
                                        · linarith only [h149, hlam, p136_0]
                                      · linarith only [h148, h2, hlam]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      rcases p136_3 (m.d 0 2) (by simp) with h157 | h157
                                      · rcases p136_3 (m.d 1 2) (by simp) with h158 | h158
                                        · rcases p136_3 (m.d 2 3) (by simp) with h159 | h159
                                          · linarith only [h159, h8, hlam]
                                          · rcases p136_3 (m.d 2 4) (by simp) with h161 | h161
                                            · linarith only [h161, hlam, p136_0]
                                            · rcases p136_3 (m.d 2 5) (by simp) with h163 | h163
                                              · linarith only [h10, h163, hlam]
                                              · linarith only [h133, h163, hlam]
                                        · linarith only [h158, hlam, p136_0]
                                      · linarith only [h157, h3, hlam]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p136_1, u5ehi2]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [h2, hlam, p136_0]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [h8, hlam, p136_0]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [hlam, p136_0]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [h129, hlam, p136_0]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [h131, hlam, p136_0]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [h3, hlam, p136_0]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [h9, hlam, p136_0]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [h133, h135, h2, h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p136_1]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [hlam, p136_0]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [h133, hlam, p136_1]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [h4, hlam, p136_0]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [h10, hlam, p136_0]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p136_1]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [h0, h10, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p136_1]
                                    · have p136_0 := h136c.1
                                      have p136_1 := h136c.2.1
                                      have p136_2 := h136c.2.2.1
                                      have p136_3 := h136c.2.2.2
                                      linarith only [hlam, p136_0]
                                  · rcases h2bigk with h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht5b, p184_1, u5ehi2]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h11, h135, h2, h5, h7, h8, hlam, p184_2]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      rcases p184_3 (m.d 0 2) (by simp) with h188 | h188
                                      · rcases p184_3 (m.d 1 2) (by simp) with h189 | h189
                                        · linarith only [h0, h189, hlam]
                                        · linarith only [h189, h9, hlam]
                                      · linarith only [h188, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      rcases p184_3 (m.d 0 2) (by simp) with h193 | h193
                                      · rcases p184_3 (m.d 1 2) (by simp) with h194 | h194
                                        · linarith only [h0, h194, hlam]
                                        · linarith only [h10, h194, hlam]
                                      · linarith only [h193, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h0, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      rcases p184_3 (m.d 0 2) (by simp) with h200 | h200
                                      · rcases p184_3 (m.d 1 2) (by simp) with h201 | h201
                                        · rcases p184_3 (m.d 2 3) (by simp) with h202 | h202
                                          · linarith only [h202, hlam, p184_0]
                                          · rcases p184_3 (m.d 2 4) (by simp) with h204 | h204
                                            · linarith only [h204, h9, hlam]
                                            · linarith only [h129, h204, hlam]
                                        · linarith only [h201, hlam, p184_0]
                                      · linarith only [h2, h200, hlam]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      rcases p184_3 (m.d 0 2) (by simp) with h209 | h209
                                      · rcases p184_3 (m.d 1 2) (by simp) with h210 | h210
                                        · rcases p184_3 (m.d 2 3) (by simp) with h211 | h211
                                          · linarith only [h211, h8, hlam]
                                          · rcases p184_3 (m.d 2 4) (by simp) with h213 | h213
                                            · linarith only [h213, hlam, p184_0]
                                            · rcases p184_3 (m.d 2 5) (by simp) with h215 | h215
                                              · linarith only [h10, h215, hlam]
                                              · linarith only [h133, h215, hlam]
                                        · linarith only [h210, hlam, p184_0]
                                      · linarith only [h209, h3, hlam]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p184_1, u5ehi2]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h2, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h8, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h129, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h131, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h3, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h9, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p184_1]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h133, hlam, p184_1]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h4, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h10, hlam, p184_0]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p184_1]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [h0, h10, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p184_1]
                                    · have p184_0 := h184c.1
                                      have p184_1 := h184c.2.1
                                      have p184_2 := h184c.2.2.1
                                      have p184_3 := h184c.2.2.2
                                      linarith only [hlam, p184_0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h236 | h236
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h237 | h237
                          · linarith only [h0, h10, h237, h4, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                            · linarith only [h0, h10, h239, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h10, h236, h239, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h242 | h242
                          · linarith only [h0, h10, h236, h242, h4, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
                            · linarith only [h0, h10, h236, h244, h4, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h246 | h246
                              · linarith only [h0, h2, h236, h242, h246, h5, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h248 | h248
                                · linarith only [h0, h10, h2, h246, h248, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h250 | h250
                                  · linarith only [h10, h244, h248, h250, h9, hc23, hc34, hlam, hphi]
                                  · rcases h2bigk with h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [hlam, p252_0]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      rcases p252_3 (m.d 0 2) (by simp) with h254 | h254
                                      · rcases p252_3 (m.d 1 2) (by simp) with h255 | h255
                                        · linarith only [h0, h255, hlam]
                                        · rcases p252_3 (m.d 2 3) (by simp) with h257 | h257
                                          · linarith only [h2, h257, hlam]
                                          · rcases p252_3 (m.d 2 4) (by simp) with h259 | h259
                                            · linarith only [h259, h3, hlam]
                                            · rcases p252_3 (m.d 2 5) (by simp) with h261 | h261
                                              · linarith only [h261, h4, hlam]
                                              · linarith only [h10, h261, hlam]
                                      · linarith only [h0, h254, hlam]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [h10, h2, h244, h246, h250, h5, h7, h9, hlam, p252_2]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [h10, h2, h246, h250, h5, h7, h9, hlam, p252_2]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [h0, h10, h244, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p252_1]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [h0, hlam, p252_0]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [hlam, p252_0]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [h10, h246, h250, h5, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p252_1]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [h10, h246, h250, h5, h7, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p252_1]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [h10, hlam, p252_0]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [h2, hlam, p252_0]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [h8, hlam, p252_0]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [hlam, p252_0]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [h244, hlam, p252_0]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [h246, hlam, p252_0]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [h3, hlam, p252_0]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [h9, hlam, p252_0]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [h0, h10, h2, h246, h250, h5, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p252_1]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [hlam, p252_0]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [h248, hlam, p252_1]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [h4, hlam, p252_0]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [h0, h2, h246, h250, h5, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p252_1]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      rcases p252_3 (m.d 0 2) (by simp) with h285 | h285
                                      · rcases p252_3 (m.d 1 2) (by simp) with h286 | h286
                                        · linarith only [h10, h286, hlam]
                                        · linarith only [h286, h8, hlam]
                                      · linarith only [h2, h285, hlam]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      rcases p252_3 (m.d 0 2) (by simp) with h290 | h290
                                      · rcases p252_3 (m.d 1 2) (by simp) with h291 | h291
                                        · linarith only [h10, h291, hlam]
                                        · linarith only [h291, h9, hlam]
                                      · linarith only [h290, h3, hlam]
                                    · have p252_0 := h252c.1
                                      have p252_1 := h252c.2.1
                                      have p252_2 := h252c.2.2.1
                                      have p252_3 := h252c.2.2.2
                                      linarith only [hlam, p252_0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h296 | h296
                      · linarith only [h0, h296, h3, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h298 | h298
                        · linarith only [h298, h8, h9, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h300 | h300
                          · linarith only [h0, h3, h300, h8, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h302 | h302
                            · linarith only [h0, h298, h3, h302, h8, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h304 | h304
                              · linarith only [h296, h300, h304, h8, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h306 | h306
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h307 | h307
                                  · rcases h2bigk with h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      rcases p308_3 (m.d 0 2) (by simp) with h310 | h310
                                      · rcases p308_3 (m.d 1 2) (by simp) with h311 | h311
                                        · linarith only [h0, h311, hlam]
                                        · rcases p308_3 (m.d 2 3) (by simp) with h313 | h313
                                          · linarith only [h2, h313, hlam]
                                          · rcases p308_3 (m.d 2 4) (by simp) with h315 | h315
                                            · linarith only [h3, h315, hlam]
                                            · linarith only [h315, h9, hlam]
                                      · linarith only [h0, h310, hlam]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h2, h296, h302, h306, h5, h8, hlam, p308_2]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h0, h296, h306, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p308_1]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h0, h296, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p308_1]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h0, hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h296, h302, h306, hc23, hc34, hlam, hphi, p308_1]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h9, hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h296, hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h2, hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h8, hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h302, hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h304, hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h3, hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h0, h3, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p308_1]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      rcases p308_3 (m.d 0 2) (by simp) with h334 | h334
                                      · rcases p308_3 (m.d 1 2) (by simp) with h335 | h335
                                        · linarith only [h335, h9, hlam]
                                        · linarith only [h335, h8, hlam]
                                      · linarith only [h2, h334, hlam]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h0, h2, h302, h5, hc01, hlam, hphi, ht0b, ht5b, p308_1, u5ehi2]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h4, hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h0, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p308_1]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      rcases p308_3 (m.d 0 2) (by simp) with h343 | h343
                                      · rcases p308_3 (m.d 1 2) (by simp) with h344 | h344
                                        · linarith only [h296, h344, hlam]
                                        · linarith only [h344, h8, hlam]
                                      · linarith only [h2, h343, hlam]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h306, hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [hlam, p308_0]
                                  · linarith only [h302, h306, h307, hlam]
                                · linarith only [h0, h2, h306, h5, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h352 | h352
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h353 | h353
                      · linarith only [h0, h2, h353, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h355 | h355
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h356 | h356
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h357 | h357
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h358 | h358
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h359 | h359
                                · linarith only [h0, h2, h352, h353, h358, h359, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h361 | h361
                                  · linarith only [h352, h353, h357, h359, h361, hlam]
                                  · rcases h2bigk with h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [hlam, p363_0]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      rcases p363_3 (m.d 0 2) (by simp) with h365 | h365
                                      · rcases p363_3 (m.d 1 2) (by simp) with h366 | h366
                                        · linarith only [h0, h366, hlam]
                                        · rcases p363_3 (m.d 2 3) (by simp) with h368 | h368
                                          · linarith only [h2, h368, hlam]
                                          · linarith only [h368, h8, hlam]
                                      · linarith only [h0, h365, hlam]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [h0, h352, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p363_1]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [h2, h352, h8, hlam, p363_2]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [h0, h352, h353, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p363_1]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [h0, hlam, p363_0]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [hlam, p363_0]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [h8, hlam, p363_0]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [h0, h353, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p363_1]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [h353, hlam, p363_0]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [h2, hlam, p363_0]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [h0, h2, h352, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p363_1]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [hlam, p363_0]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      rcases p363_3 (m.d 0 2) (by simp) with h383 | h383
                                      · rcases p363_3 (m.d 1 2) (by simp) with h384 | h384
                                        · linarith only [h384, h8, hlam]
                                        · linarith only [h352, h384, hlam]
                                      · linarith only [h3, h383, hlam]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht5b, p363_1, u5ehi2]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [h3, hlam, p363_0]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [h352, hlam, p363_0]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [h357, hlam, p363_1]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [hlam, p363_0]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [h359, hlam, p363_1]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [h4, hlam, p363_0]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [h0, h352, h357, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p363_1]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [h358, hlam, p363_1]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      rcases p363_3 (m.d 0 2) (by simp) with h397 | h397
                                      · rcases p363_3 (m.d 1 2) (by simp) with h398 | h398
                                        · linarith only [h353, h398, hlam]
                                        · linarith only [h352, h398, hlam]
                                      · linarith only [h3, h397, hlam]
                                    · have p363_0 := h363c.1
                                      have p363_1 := h363c.2.1
                                      have p363_2 := h363c.2.2.1
                                      have p363_3 := h363c.2.2.2
                                      linarith only [hlam, p363_0]
                              · linarith only [h352, h356, h357, h358, h8, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h2, h352, h357, h5, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h405 | h405
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h406 | h406
                              · linarith only [h0, h2, h352, h356, h405, h406, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · linarith only [h0, h2, h352, h405, h406, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h2, h352, h405, h5, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h352, h355, h8, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h411 | h411
                      · linarith only [h0, h3, h352, h411, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h413 | h413
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h414 | h414
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h415 | h415
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h416 | h416
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h417 | h417
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h418 | h418
                                  · linarith only [h1, h413, h418, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases h2bigk with h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [hlam, p420_0]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      rcases p420_3 (m.d 0 2) (by simp) with h422 | h422
                                      · rcases p420_3 (m.d 1 2) (by simp) with h423 | h423
                                        · linarith only [h0, h423, hlam]
                                        · rcases p420_3 (m.d 2 3) (by simp) with h425 | h425
                                          · linarith only [h2, h425, hlam]
                                          · linarith only [h425, h8, hlam]
                                      · linarith only [h0, h422, hlam]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [h0, h415, h417, h418, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p420_1]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [h0, h417, h418, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p420_1]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      rcases p420_3 (m.d 0 2) (by simp) with h431 | h431
                                      · rcases p420_3 (m.d 1 2) (by simp) with h432 | h432
                                        · linarith only [h0, h432, hlam]
                                        · rcases p420_3 (m.d 2 3) (by simp) with h434 | h434
                                          · linarith only [h2, h434, hlam]
                                          · linarith only [h416, h434, hlam]
                                      · linarith only [h431, hlam, p420_0]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [h0, hlam, p420_0]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [hlam, p420_0]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [h8, hlam, p420_0]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [h352, hlam, p420_0]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [h411, hlam, p420_0]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [h2, hlam, p420_0]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      rcases p420_3 (m.d 0 2) (by simp) with h444 | h444
                                      · rcases p420_3 (m.d 1 2) (by simp) with h445 | h445
                                        · linarith only [h445, hlam, p420_0]
                                        · rcases p420_3 (m.d 2 3) (by simp) with h447 | h447
                                          · rcases p420_3 (m.d 2 4) (by simp) with h448 | h448
                                            · linarith only [h415, h448, hlam]
                                            · linarith only [h352, h448, hlam]
                                          · linarith only [h447, hlam, p420_0]
                                      · linarith only [h0, h444, hlam]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [hlam, p420_0]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [h417, h418, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p420_1]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [h0, h2, h411, hc01, hlam, hphi, ht0b, ht5b, p420_1, u5ehi1]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [h3, hlam, p420_0]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      rcases p420_3 (m.d 0 2) (by simp) with h457 | h457
                                      · rcases p420_3 (m.d 1 2) (by simp) with h458 | h458
                                        · linarith only [h458, hlam, p420_0]
                                        · rcases p420_3 (m.d 2 3) (by simp) with h460 | h460
                                          · rcases p420_3 (m.d 2 4) (by simp) with h461 | h461
                                            · rcases p420_3 (m.d 2 5) (by simp) with h462 | h462
                                              · linarith only [h417, h462, hlam]
                                              · linarith only [h411, h462, hlam]
                                            · linarith only [h461, hlam, p420_0]
                                          · linarith only [h460, h8, hlam]
                                      · linarith only [h0, h457, hlam]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [h415, hlam, p420_1]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [hlam, p420_0]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [h0, h2, h411, h415, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p420_1]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [h4, hlam, p420_0]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      rcases p420_3 (m.d 0 2) (by simp) with h472 | h472
                                      · rcases p420_3 (m.d 1 2) (by simp) with h473 | h473
                                        · linarith only [h473, hlam, p420_0]
                                        · rcases p420_3 (m.d 2 3) (by simp) with h475 | h475
                                          · rcases p420_3 (m.d 2 4) (by simp) with h476 | h476
                                            · rcases p420_3 (m.d 2 5) (by simp) with h477 | h477
                                              · rcases h3bigk with h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [hlam, p478_0]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [h0, h2, h414, hc01, hlam, hphi, ht0b, ht5b, p478_1, u5ehi3]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [h0, h2, h414, h8, hc01, hlam, hphi, ht0b, ht5b, p478_1, u5ehi3]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  rcases p478_3 (m.d 0 3) (by simp) with h482 | h482
                                                  · rcases p478_3 (m.d 1 3) (by simp) with h483 | h483
                                                    · linarith only [h1, h483, hlam]
                                                    · linarith only [h413, h483, hlam]
                                                  · linarith only [h482, hlam, p478_0]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  rcases p478_3 (m.d 0 3) (by simp) with h487 | h487
                                                  · rcases p478_3 (m.d 1 3) (by simp) with h488 | h488
                                                    · linarith only [h1, h488, hlam]
                                                    · linarith only [h414, h488, hlam]
                                                  · linarith only [h487, hlam, p478_0]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [h1, hlam, p478_0]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [hlam, p478_0]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [h8, hlam, p478_1]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  rcases p478_3 (m.d 0 3) (by simp) with h495 | h495
                                                  · rcases p478_3 (m.d 1 3) (by simp) with h496 | h496
                                                    · rcases p478_3 (m.d 2 3) (by simp) with h497 | h497
                                                      · rcases p478_3 (m.d 3 4) (by simp) with h498 | h498
                                                        · linarith only [h498, hlam, p478_0]
                                                        · rcases p478_3 (m.d 3 5) (by simp) with h500 | h500
                                                          · linarith only [h414, h500, hlam]
                                                          · linarith only [h418, h500, hlam]
                                                      · linarith only [h415, h497, hlam]
                                                    · linarith only [h496, hlam, p478_0]
                                                  · linarith only [h495, h5, hlam]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p478_1, u5ehi3]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [h2, hlam, p478_0]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [h0, h2, h413, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p478_1]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [hlam, p478_0]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  rcases p478_3 (m.d 0 3) (by simp) with h510 | h510
                                                  · rcases p478_3 (m.d 1 3) (by simp) with h511 | h511
                                                    · linarith only [h511, h8, hlam]
                                                    · linarith only [h413, h511, hlam]
                                                  · linarith only [h5, h510, hlam]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht5b, p478_1, u5ehi3]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [h5, hlam, p478_0]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [h413, hlam, p478_0]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [h415, hlam, p478_0]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [hlam, p478_0]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [h418, hlam, p478_1]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [h6, hlam, p478_0]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [h414, hlam, p478_0]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [h416, hlam, p478_0]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [h1, h414, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p478_1]
                                                · have p478_0 := h478c.1
                                                  have p478_1 := h478c.2.1
                                                  have p478_2 := h478c.2.2.1
                                                  have p478_3 := h478c.2.2.2
                                                  linarith only [hlam, p478_0]
                                              · linarith only [h477, hlam, p420_0]
                                            · linarith only [h352, h476, hlam]
                                          · linarith only [h475, h8, hlam]
                                      · linarith only [h0, h472, hlam]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [h416, hlam, p420_1]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [h417, hlam, p420_0]
                                    · have p420_0 := h420c.1
                                      have p420_1 := h420c.2.1
                                      have p420_2 := h420c.2.2.1
                                      have p420_3 := h420c.2.2.2
                                      linarith only [hlam, p420_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h533 | h533
                                  · linarith only [h352, h417, h533, hc12, hc34, hlam, hphi, ht23]
                                  · rcases h2bigk with h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [hlam, p535_0]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [h2, h352, h417, h5, h7, hlam, p535_2]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [h414, h8, hc02, hlam, hphi, ht0b, ht5b, p535_1, u5ehi3]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      rcases p535_3 (m.d 0 2) (by simp) with h539 | h539
                                      · rcases p535_3 (m.d 1 2) (by simp) with h540 | h540
                                        · linarith only [h0, h540, hlam]
                                        · rcases p535_3 (m.d 2 3) (by simp) with h542 | h542
                                          · linarith only [h2, h542, hlam]
                                          · linarith only [h415, h542, hlam]
                                      · linarith only [h539, hlam, p535_0]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      rcases p535_3 (m.d 0 2) (by simp) with h546 | h546
                                      · rcases p535_3 (m.d 1 2) (by simp) with h547 | h547
                                        · linarith only [h0, h547, hlam]
                                        · rcases p535_3 (m.d 2 3) (by simp) with h549 | h549
                                          · linarith only [h2, h549, hlam]
                                          · linarith only [h416, h549, hlam]
                                      · linarith only [h546, hlam, p535_0]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [h0, hlam, p535_0]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [hlam, p535_0]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [h8, hlam, p535_0]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [h352, hlam, p535_0]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [h411, hlam, p535_0]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [h2, hlam, p535_0]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      rcases p535_3 (m.d 0 2) (by simp) with h559 | h559
                                      · rcases p535_3 (m.d 1 2) (by simp) with h560 | h560
                                        · linarith only [h560, hlam, p535_0]
                                        · rcases p535_3 (m.d 2 3) (by simp) with h562 | h562
                                          · rcases p535_3 (m.d 2 4) (by simp) with h563 | h563
                                            · linarith only [h415, h563, hlam]
                                            · linarith only [h352, h563, hlam]
                                          · linarith only [h562, hlam, p535_0]
                                      · linarith only [h0, h559, hlam]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [hlam, p535_0]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [h352, hc12, hc23, hlam, hphi, p535_1]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht5b, p535_1, u5ehi2]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [h3, hlam, p535_0]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [h0, h2, h417, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p535_1]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [h415, hlam, p535_1]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [hlam, p535_0]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [h417, hlam, p535_1]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [h4, hlam, p535_0]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      rcases p535_3 (m.d 0 2) (by simp) with h577 | h577
                                      · rcases p535_3 (m.d 1 2) (by simp) with h578 | h578
                                        · linarith only [h578, hlam, p535_0]
                                        · rcases p535_3 (m.d 2 3) (by simp) with h580 | h580
                                          · rcases p535_3 (m.d 2 4) (by simp) with h581 | h581
                                            · linarith only [h417, h581, hlam]
                                            · linarith only [h352, h581, hlam]
                                          · linarith only [h580, h8, hlam]
                                      · linarith only [h0, h577, hlam]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [h416, hlam, p535_1]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [h0, h352, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p535_1]
                                    · have p535_0 := h535c.1
                                      have p535_1 := h535c.2.1
                                      have p535_2 := h535c.2.2.1
                                      have p535_3 := h535c.2.2.2
                                      linarith only [hlam, p535_0]
                              · linarith only [h1, h414, h416, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h0, h3, h352, h413, h414, h415, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h591 | h591
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h592 | h592
                              · linarith only [h0, h2, h413, h414, h592, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h594 | h594
                                · linarith only [h0, h2, h591, h592, h594, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h596 | h596
                                  · linarith only [h1, h413, h594, h596, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                                  · rcases h2bigk with h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [hlam, p598_0]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [h2, h5, h592, h596, h7, h8, hlam, p598_2]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      rcases p598_3 (m.d 0 2) (by simp) with h601 | h601
                                      · rcases p598_3 (m.d 1 2) (by simp) with h602 | h602
                                        · linarith only [h0, h602, hlam]
                                        · rcases p598_3 (m.d 2 3) (by simp) with h604 | h604
                                          · linarith only [h604, hlam, p598_0]
                                          · rcases p598_3 (m.d 2 4) (by simp) with h606 | h606
                                            · linarith only [h3, h606, hlam]
                                            · rcases p598_3 (m.d 2 5) (by simp) with h608 | h608
                                              · linarith only [h4, h608, hlam]
                                              · linarith only [h592, h608, hlam]
                                      · linarith only [h601, hlam, p598_0]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      rcases p598_3 (m.d 0 2) (by simp) with h612 | h612
                                      · rcases p598_3 (m.d 1 2) (by simp) with h613 | h613
                                        · linarith only [h0, h613, hlam]
                                        · rcases p598_3 (m.d 2 3) (by simp) with h615 | h615
                                          · linarith only [h2, h615, hlam]
                                          · linarith only [h591, h615, hlam]
                                      · linarith only [h612, hlam, p598_0]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      rcases p598_3 (m.d 0 2) (by simp) with h619 | h619
                                      · rcases p598_3 (m.d 1 2) (by simp) with h620 | h620
                                        · linarith only [h0, h620, hlam]
                                        · rcases p598_3 (m.d 2 3) (by simp) with h622 | h622
                                          · linarith only [h2, h622, hlam]
                                          · rcases p598_3 (m.d 2 4) (by simp) with h624 | h624
                                            · linarith only [h3, h624, hlam]
                                            · rcases p598_3 (m.d 2 5) (by simp) with h626 | h626
                                              · linarith only [h626, hlam, p598_0]
                                              · rcases h3bigk with h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [hlam, p628_0]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  rcases p628_3 (m.d 0 3) (by simp) with h630 | h630
                                                  · rcases p628_3 (m.d 1 3) (by simp) with h631 | h631
                                                    · linarith only [h1, h631, hlam]
                                                    · rcases p628_3 (m.d 2 3) (by simp) with h633 | h633
                                                      · linarith only [h2, h633, hlam]
                                                      · linarith only [h633, h8, hlam]
                                                  · linarith only [h1, h630, hlam]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  rcases p628_3 (m.d 0 3) (by simp) with h637 | h637
                                                  · rcases p628_3 (m.d 1 3) (by simp) with h638 | h638
                                                    · linarith only [h1, h638, hlam]
                                                    · rcases p628_3 (m.d 2 3) (by simp) with h640 | h640
                                                      · linarith only [h2, h640, hlam]
                                                      · rcases p628_3 (m.d 3 4) (by simp) with h642 | h642
                                                        · linarith only [h5, h642, hlam]
                                                        · rcases p628_3 (m.d 3 5) (by simp) with h644 | h644
                                                          · linarith only [h6, h644, hlam]
                                                          · linarith only [h592, h644, hlam]
                                                  · linarith only [h2, h637, hlam]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [h413, h5, h592, h596, h7, h8, hlam, p628_2]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [h0, h2, h352, h591, h592, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p628_1]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [h1, hlam, p628_0]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [hlam, p628_0]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [h8, hlam, p628_1]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [h0, h411, h414, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p598_1, p628_1]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [h414, hlam, p628_0]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [h2, hlam, p628_0]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [h592, hc13, hc35, hlam, hphi, p628_1]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [hlam, p628_0]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [h0, h2, h592, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p628_1]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [h592, hlam, p628_0]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [h5, hlam, p628_0]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [h413, hlam, p628_0]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [h591, hlam, p628_0]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [hlam, p628_0]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [h596, hlam, p628_1]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [h6, hlam, p628_0]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [h0, h2, h413, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p628_1]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [h0, h2, h352, h591, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p628_1]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  rcases p628_3 (m.d 0 3) (by simp) with h668 | h668
                                                  · rcases p628_3 (m.d 1 3) (by simp) with h669 | h669
                                                    · linarith only [h414, h669, hlam]
                                                    · linarith only [h413, h669, hlam]
                                                  · linarith only [h5, h668, hlam]
                                                · have p628_0 := h628c.1
                                                  have p628_1 := h628c.2.1
                                                  have p628_2 := h628c.2.2.1
                                                  have p628_3 := h628c.2.2.2
                                                  linarith only [hlam, p628_0]
                                      · linarith only [h619, hlam, p598_0]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [h0, hlam, p598_0]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [hlam, p598_0]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [h8, hlam, p598_0]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [h352, hlam, p598_0]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [h411, hlam, p598_0]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [h2, hlam, p598_0]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [h0, h2, h5, h592, h596, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p598_1]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [hlam, p598_0]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [h352, hc12, hc23, hlam, hphi, p598_1]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [h592, hlam, p598_0]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [h3, hlam, p598_0]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [h0, h2, h5, h591, h592, h596, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p598_1]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [h591, hlam, p598_1]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [hlam, p598_0]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [h594, hlam, p598_1]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [h4, hlam, p598_0]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      rcases p598_3 (m.d 0 2) (by simp) with h691 | h691
                                      · rcases p598_3 (m.d 1 2) (by simp) with h692 | h692
                                        · linarith only [h692, hlam, p598_0]
                                        · rcases p598_3 (m.d 2 3) (by simp) with h694 | h694
                                          · linarith only [h592, h694, hlam]
                                          · linarith only [h694, h8, hlam]
                                      · linarith only [h0, h691, hlam]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [h0, h2, h5, h592, h596, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p598_1]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [h0, h2, h352, h5, h592, h596, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p598_1]
                                    · have p598_0 := h598c.1
                                      have p598_1 := h598c.2.1
                                      have p598_2 := h598c.2.2.1
                                      have p598_3 := h598c.2.2.2
                                      linarith only [hlam, p598_0]
                            · linarith only [h1, h413, h591, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h702 | h702
                          · linarith only [h0, h2, h413, h5, h702, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h704 | h704
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h705 | h705
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h706 | h706
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h707 | h707
                                  · linarith only [h0, h2, h704, h707, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · linarith only [h0, h3, h413, h706, h707, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h710 | h710
                                  · linarith only [h0, h2, h352, h5, h706, h710, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                  · rcases h2bigk with h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [hlam, p712_0]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [h2, h413, h5, h7, h704, h706, h8, hlam, p712_2]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [h0, h702, h705, hc01, hlam, hphi, ht0b, ht5b, p712_1, u5ehi1]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      rcases p712_3 (m.d 0 2) (by simp) with h716 | h716
                                      · rcases p712_3 (m.d 1 2) (by simp) with h717 | h717
                                        · linarith only [h0, h717, hlam]
                                        · rcases p712_3 (m.d 2 3) (by simp) with h719 | h719
                                          · linarith only [h2, h719, hlam]
                                          · linarith only [h704, h719, hlam]
                                      · linarith only [h716, hlam, p712_0]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      rcases p712_3 (m.d 0 2) (by simp) with h723 | h723
                                      · rcases p712_3 (m.d 1 2) (by simp) with h724 | h724
                                        · linarith only [h0, h724, hlam]
                                        · rcases p712_3 (m.d 2 3) (by simp) with h726 | h726
                                          · linarith only [h2, h726, hlam]
                                          · linarith only [h705, h726, hlam]
                                      · linarith only [h723, hlam, p712_0]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [h0, hlam, p712_0]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [hlam, p712_0]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [h8, hlam, p712_0]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [h352, hlam, p712_0]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [h411, hlam, p712_0]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [h2, hlam, p712_0]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      rcases p712_3 (m.d 0 2) (by simp) with h736 | h736
                                      · rcases p712_3 (m.d 1 2) (by simp) with h737 | h737
                                        · linarith only [h737, hlam, p712_0]
                                        · rcases p712_3 (m.d 2 3) (by simp) with h739 | h739
                                          · rcases p712_3 (m.d 2 4) (by simp) with h740 | h740
                                            · linarith only [h704, h740, hlam]
                                            · linarith only [h352, h740, hlam]
                                          · linarith only [h739, hlam, p712_0]
                                      · linarith only [h0, h736, hlam]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [hlam, p712_0]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [h413, h704, h8, hc12, hc23, hlam, hphi, p712_1]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht5b, p712_1, u5ehi2]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [h3, hlam, p712_0]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [h0, h2, h5, h7, h706, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p712_1]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [h704, hlam, p712_1]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [hlam, p712_0]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [h706, hlam, p712_1]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [h4, hlam, p712_0]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      rcases p712_3 (m.d 0 2) (by simp) with h754 | h754
                                      · rcases p712_3 (m.d 1 2) (by simp) with h755 | h755
                                        · linarith only [h755, hlam, p712_0]
                                        · rcases p712_3 (m.d 2 3) (by simp) with h757 | h757
                                          · rcases p712_3 (m.d 2 4) (by simp) with h758 | h758
                                            · linarith only [h706, h758, hlam]
                                            · linarith only [h352, h758, hlam]
                                          · linarith only [h757, h8, hlam]
                                      · linarith only [h0, h754, hlam]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [h705, hlam, p712_1]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [h0, h4, h413, h704, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p712_1]
                                    · have p712_0 := h712c.1
                                      have p712_1 := h712c.2.1
                                      have p712_2 := h712c.2.2.1
                                      have p712_3 := h712c.2.2.2
                                      linarith only [hlam, p712_0]
                              · linarith only [h0, h2, h413, h6, h704, h705, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h767 | h767
                              · linarith only [h0, h2, h5, h704, h767, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h769 | h769
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h770 | h770
                                  · rcases h2bigk with h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [hlam, p771_0]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [h2, h5, h767, h770, h8, hlam, p771_2]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      rcases p771_3 (m.d 0 2) (by simp) with h774 | h774
                                      · rcases p771_3 (m.d 1 2) (by simp) with h775 | h775
                                        · linarith only [h0, h775, hlam]
                                        · rcases p771_3 (m.d 2 3) (by simp) with h777 | h777
                                          · linarith only [h777, hlam, p771_0]
                                          · rcases p771_3 (m.d 2 4) (by simp) with h779 | h779
                                            · linarith only [h3, h779, hlam]
                                            · linarith only [h704, h779, hlam]
                                      · linarith only [h774, hlam, p771_0]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [h0, h769, hc01, hlam, hphi, ht0b, ht5b, p771_1, u5ehi4]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      rcases p771_3 (m.d 0 2) (by simp) with h784 | h784
                                      · rcases p771_3 (m.d 1 2) (by simp) with h785 | h785
                                        · linarith only [h0, h785, hlam]
                                        · rcases p771_3 (m.d 2 3) (by simp) with h787 | h787
                                          · linarith only [h2, h787, hlam]
                                          · rcases p771_3 (m.d 2 4) (by simp) with h789 | h789
                                            · linarith only [h3, h789, hlam]
                                            · linarith only [h769, h789, hlam]
                                      · linarith only [h784, hlam, p771_0]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [h0, hlam, p771_0]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [hlam, p771_0]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [h8, hlam, p771_0]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [h352, hlam, p771_0]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [h411, hlam, p771_0]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [h2, hlam, p771_0]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [h0, h2, h5, h767, h770, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p771_1]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [hlam, p771_0]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [h704, hlam, p771_0]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [h767, hlam, p771_0]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [h3, hlam, p771_0]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      rcases p771_3 (m.d 0 2) (by simp) with h804 | h804
                                      · rcases p771_3 (m.d 1 2) (by simp) with h805 | h805
                                        · linarith only [h805, hlam, p771_0]
                                        · rcases p771_3 (m.d 2 3) (by simp) with h807 | h807
                                          · linarith only [h704, h807, hlam]
                                          · linarith only [h8, h807, hlam]
                                      · linarith only [h0, h804, hlam]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [h8, hc12, hc24, hlam, hphi, p771_1]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [hlam, p771_0]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [h0, h2, h5, h704, hc01, hlam, hphi, ht0b, ht5b, p771_1, u5ehi2]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [h4, hlam, p771_0]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      rcases p771_3 (m.d 0 2) (by simp) with h815 | h815
                                      · rcases p771_3 (m.d 1 2) (by simp) with h816 | h816
                                        · linarith only [h816, hlam, p771_0]
                                        · rcases p771_3 (m.d 2 3) (by simp) with h818 | h818
                                          · linarith only [h767, h818, hlam]
                                          · linarith only [h8, h818, hlam]
                                      · linarith only [h0, h815, hlam]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [h8, hc12, hc25, hlam, hphi, p771_1]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [h769, hlam, p771_0]
                                    · have p771_0 := h771c.1
                                      have p771_1 := h771c.2.1
                                      have p771_2 := h771c.2.2.1
                                      have p771_3 := h771c.2.2.2
                                      linarith only [hlam, p771_0]
                                  · linarith only [h0, h2, h5, h7, h704, h770, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h826 | h826
                                  · linarith only [h0, h2, h352, h5, h769, h826, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                  · linarith only [h0, h2, h5, h7, h704, h8, h826, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
              · linarith only [h6, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
            · linarith only [h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
          · linarith only [h4, hc25, hlam, hphi, ht01, ht12, u0ehi1]
        · linarith only [h2, h3, hc24, hlam, hphi, ht01, ht12, u0ehi2]
      · linarith only [h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]
    · linarith only [h1, hc13, hlam, hphi, ht01, u0ehi0]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

end R2N4
