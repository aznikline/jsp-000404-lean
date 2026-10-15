import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_58S6
import Jsp000404.R1LeavesN7_58S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3690000 in
set_option maxHeartbeats 3690000 in
theorem r1l7_13_24_L_R_M_IR (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3ehi := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_13_24_L_R_M_IR_x0 m hb3 hb4 h0
  · exact r1l7_13_24_L_R_M_IR_x1 m hb3 hb4 h0

set_option maxHeartbeats 3642000 in
set_option maxHeartbeats 3642000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_0_L_0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h3elo := hb3.1
  have h4elo := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
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
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                                    · linarith only [h0, h15, h18, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                    · linarith only [h18, h8, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h14, h17, h2, hc24, hlam, hphi, u4elo0]
                                · linarith only [h16, h7, hc23, hlam, hphi, u3elo0]
                              · linarith only [h15, h6, hc23, hlam, hphi, u3elo0]
                            · linarith only [h14, h8, hc14, hlam, hphi, u4elo0]
                          · linarith only [h13, h7, hc13, hlam, hphi, u3elo0]
                        · linarith only [h12, h6, h9, hc23, hlam, hphi, u3elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
                          · linarith only [h11, h28, h9, hlam]
                          · linarith only [h28, h7, hc13, hlam, hphi, u3elo0]
                        · linarith only [h27, h6, h9, hc23, hlam, hphi, u3elo0]
                    · linarith only [h10, h5, h9, hc23, hlam, hphi, ht34, u4elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36 | h36
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h37 | h37
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h40 | h40
                                  · linarith only [h33, h4, h40, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                                  · linarith only [h37, h38, h40, hc34, hlam, hphi, u4elo1]
                                · linarith only [h33, h38, h39, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                              · linarith only [h38, h9, hc12, hlam, hphi, ht23, u3elo3]
                            · linarith only [h37, h8, hc14, hlam, hphi, u4elo0]
                          · linarith only [h36, h7, hc13, hlam, hphi, u3elo0]
                        · linarith only [h35, h6, h9, hc12, hlam, hphi, ht23, u3elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                            · linarith only [h33, h34, h50, hlam]
                            · linarith only [h50, h8, hc14, hlam, hphi, u4elo0]
                          · linarith only [h49, h7, hc13, hlam, hphi, u3elo0]
                        · linarith only [h33, h48, h9, hc24, hlam, hphi, u4elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h55 | h55
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h56 | h56
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h57 | h57
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h58 | h58
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h59 | h59
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
                                    · rcases h0bigk with h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [hlam, p63_0]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [h0, h55, hc01, hc25, hlam, hphi, ht0b, ht5b, p63_1]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [h1, h56, h62, hc01, hc45, hlam, hphi, ht0b, ht5b, p63_1]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [h2, h33, h55, h60, hc01, hc35, hlam, hphi, ht0b, ht5b, p63_1]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        rcases p63_3 (m.d 0 1) (by simp) with h68 | h68
                                        · rcases p63_3 (m.d 0 2) (by simp) with h69 | h69
                                          · linarith only [h0, h69, hlam]
                                          · linarith only [h33, h4, h55, h59, h60, h62, h69, hc01, hc45, hlam, hphi, ht0b, ht5b, p63_1]
                                        · linarith only [h3, h68, hlam]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [h0, hlam, p63_0]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [hlam, p63_0]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [h33, h5, h55, h6, h60, h62, hc02, hc45, hlam, hphi, ht0b, ht5b, p63_1]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [h0, h33, h5, h55, h60, h62, hc01, hc45, hlam, hphi, ht0b, ht5b, p63_1]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        rcases p63_3 (m.d 0 1) (by simp) with h77 | h77
                                        · rcases p63_3 (m.d 0 2) (by simp) with h78 | h78
                                          · rcases p63_3 (m.d 0 3) (by simp) with h79 | h79
                                            · linarith only [h4, h79, hlam]
                                            · linarith only [h7, h79, hlam]
                                          · linarith only [h78, hlam, p63_0]
                                        · linarith only [h3, h77, hlam]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [h1, hlam, p63_1]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [h4, hlam, p63_1]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [hlam, p63_0]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [h33, h5, h55, h60, h62, hc03, hc45, hlam, hphi, ht0b, ht5b, p63_1]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p63_1, u3elo0]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [h2, hlam, p63_0]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [h5, hlam, p63_0]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [h6, hlam, p63_0]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [hlam, p63_0]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [h62, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p63_1, u4elo0]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [h3, hlam, p63_0]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [h0, h55, h60, h62, hc05, hc45, hlam, hphi, ht0b, ht5b, p63_1]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [h7, hlam, p63_0]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [h8, hlam, p63_1]
                                      · have p63_0 := h63c.1
                                        have p63_1 := h63c.2.1
                                        have p63_2 := h63c.2.2.1
                                        have p63_3 := h63c.2.2.2
                                        linarith only [hlam, p63_0]
                                    · linarith only [h62, h8, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h33, h61, hc12, hlam, hphi, ht23, ht34, u4elo4]
                                · linarith only [h33, h55, h59, h60, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                              · linarith only [h56, h59, hc23, hlam, hphi, u3elo1]
                            · linarith only [h33, h55, h58, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                          · linarith only [h57, h7, hc13, hlam, hphi, u3elo0]
                        · linarith only [h55, h56, h6, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h106 | h106
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h107 | h107
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h108 | h108
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h111 | h111
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h112 | h112
                                    · rcases h0bigk with h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [hlam, p113_0]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p113_1]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [h1, h106, h112, hc01, hc45, hlam, hphi, ht0b, ht5b, p113_1]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [h112, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p113_1]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        rcases p113_3 (m.d 0 1) (by simp) with h118 | h118
                                        · rcases p113_3 (m.d 0 2) (by simp) with h119 | h119
                                          · linarith only [h0, h119, hlam]
                                          · linarith only [h106, h112, h119, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p113_1]
                                        · linarith only [h118, h3, hlam]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [h0, hlam, p113_0]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [hlam, p113_0]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [h106, h112, h4, h9, hc02, hc45, hlam, hphi, ht0b, ht5b, p113_1]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [h0, h106, h111, h112, h4, h5, h55, h9, hc01, hc12, hc45, hlam, hphi, ht0b, ht23, ht5b, p113_1, u3elo0]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        rcases p113_3 (m.d 0 1) (by simp) with h127 | h127
                                        · rcases p113_3 (m.d 0 2) (by simp) with h128 | h128
                                          · rcases p113_3 (m.d 0 3) (by simp) with h129 | h129
                                            · linarith only [h129, h4, hlam]
                                            · linarith only [h129, h7, hlam]
                                          · linarith only [h128, hlam, p113_0]
                                        · linarith only [h127, h3, hlam]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [h1, hlam, p113_1]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [h4, hlam, p113_1]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [hlam, p113_0]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [h111, h5, h55, hc12, hlam, hphi, ht23, p113_1, u3elo0]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p113_1, u3elo0]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [h2, hlam, p113_0]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [h5, hlam, p113_0]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [h6, hlam, p113_0]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [hlam, p113_0]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [h107, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p113_1, u4elo0]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [h3, hlam, p113_0]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [h3, h4, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p113_1]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [h7, hlam, p113_0]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [h8, hlam, p113_1]
                                      · have p113_0 := h113c.1
                                        have p113_1 := h113c.2.1
                                        have p113_2 := h113c.2.2.1
                                        have p113_3 := h113c.2.2.2
                                        linarith only [hlam, p113_0]
                                    · linarith only [h112, h8, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h108, h111, h33, hlam]
                                · linarith only [h110, h7, h9, hc13, hlam, hphi, u3elo0]
                              · linarith only [h109, h9, hc12, hlam, hphi, ht23, u3elo3]
                            · linarith only [h106, h108, h8, hc34, hlam, hphi, u4elo0]
                          · linarith only [h106, h107, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · linarith only [h106, h6, hc13, hlam, hphi, u3elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h156 | h156
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h157 | h157
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h158 | h158
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h159 | h159
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h160 | h160
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h161 | h161
                            · linarith only [h161, h8, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h163 | h163
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h164 | h164
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h165 | h165
                                  · linarith only [h157, h165, h2, h8, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h167 | h167
                                    · linarith only [h167, h8, hc04, hlam, hphi, u4elo3]
                                    · rcases h0bigk with h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [hlam, p169_0]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [h0, h156, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p169_1]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [h164, h167, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p169_1]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        rcases p169_3 (m.d 0 1) (by simp) with h173 | h173
                                        · rcases p169_3 (m.d 0 2) (by simp) with h174 | h174
                                          · linarith only [h0, h174, hlam]
                                          · linarith only [h174, h5, hlam]
                                        · linarith only [h173, h2, hlam]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        rcases p169_3 (m.d 0 1) (by simp) with h178 | h178
                                        · rcases p169_3 (m.d 0 2) (by simp) with h179 | h179
                                          · linarith only [h0, h179, hlam]
                                          · linarith only [h0, h156, h164, h167, h179, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p169_1]
                                        · linarith only [h178, h3, hlam]
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
                                        linarith only [h1, h156, h164, h167, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p169_1]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        rcases p169_3 (m.d 0 1) (by simp) with h186 | h186
                                        · rcases p169_3 (m.d 0 2) (by simp) with h187 | h187
                                          · rcases p169_3 (m.d 0 3) (by simp) with h188 | h188
                                            · linarith only [h188, h4, hlam]
                                            · linarith only [h188, h6, hlam]
                                          · linarith only [h187, h5, hlam]
                                        · linarith only [h186, h2, hlam]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        rcases p169_3 (m.d 0 1) (by simp) with h193 | h193
                                        · rcases p169_3 (m.d 0 2) (by simp) with h194 | h194
                                          · rcases p169_3 (m.d 0 3) (by simp) with h195 | h195
                                            · linarith only [h195, h4, hlam]
                                            · linarith only [h195, h7, hlam]
                                          · linarith only [h194, hlam, p169_0]
                                        · linarith only [h193, h3, hlam]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [h1, hlam, p169_1]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [h4, hlam, p169_1]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [hlam, p169_0]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p169_1, u3elo0]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p169_1, u3elo0]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [h2, hlam, p169_0]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [h5, hlam, p169_0]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [h6, hlam, p169_0]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [hlam, p169_0]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [h8, hlam, p169_0]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [h3, hlam, p169_0]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [h0, h156, h164, h167, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p169_1]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [h7, hlam, p169_0]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [h157, h163, h2, h8, hc34, hlam, hphi, p169_1, u4elo4]
                                      · have p169_0 := h169c.1
                                        have p169_1 := h169c.2.1
                                        have p169_2 := h169c.2.2.1
                                        have p169_3 := h169c.2.2.2
                                        linarith only [hlam, p169_0]
                                · linarith only [h164, h7, hc23, hlam, hphi, u3elo0]
                              · linarith only [h159, h163, hc23, hlam, hphi, u3elo1]
                          · linarith only [h160, h7, hc13, hlam, hphi, u3elo0]
                        · linarith only [h156, h159, h6, hc23, hlam, hphi, u3elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h219 | h219
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h220 | h220
                          · linarith only [h156, h158, h220, hlam]
                          · linarith only [h220, h7, hc13, hlam, hphi, u3elo0]
                        · linarith only [h156, h219, h6, hc23, hlam, hphi, u3elo0]
                    · linarith only [h156, h157, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h225 | h225
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h226 | h226
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h227 | h227
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h228 | h228
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h229 | h229
                            · linarith only [h2, h229, h8, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h231 | h231
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h232 | h232
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h233 | h233
                                  · linarith only [h156, h225, h233, h4, h8, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h235 | h235
                                    · linarith only [h2, h225, h231, h235, h8, hlam]
                                    · rcases h0bigk with h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [hlam, p237_0]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [h0, h226, hc01, hc25, hlam, hphi, ht0b, ht5b, p237_1]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [h1, h156, h226, h232, hc01, hc35, hlam, hphi, ht0b, ht5b, p237_1]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        rcases p237_3 (m.d 0 1) (by simp) with h241 | h241
                                        · rcases p237_3 (m.d 0 2) (by simp) with h242 | h242
                                          · linarith only [h0, h242, hlam]
                                          · linarith only [h242, h5, hlam]
                                        · linarith only [h2, h241, hlam]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        rcases p237_3 (m.d 0 1) (by simp) with h246 | h246
                                        · rcases p237_3 (m.d 0 2) (by simp) with h247 | h247
                                          · linarith only [h0, h247, hlam]
                                          · linarith only [h156, h226, h231, h233, h247, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p237_1]
                                        · linarith only [h246, h3, hlam]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [h0, hlam, p237_0]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [hlam, p237_0]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [h156, h226, h231, h233, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p237_1]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        rcases p237_3 (m.d 0 1) (by simp) with h254 | h254
                                        · rcases p237_3 (m.d 0 2) (by simp) with h255 | h255
                                          · rcases p237_3 (m.d 0 3) (by simp) with h256 | h256
                                            · linarith only [h256, h4, hlam]
                                            · linarith only [h256, h6, hlam]
                                          · linarith only [h255, h5, hlam]
                                        · linarith only [h2, h254, hlam]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        rcases p237_3 (m.d 0 1) (by simp) with h261 | h261
                                        · rcases p237_3 (m.d 0 2) (by simp) with h262 | h262
                                          · rcases p237_3 (m.d 0 3) (by simp) with h263 | h263
                                            · linarith only [h263, h4, hlam]
                                            · linarith only [h263, h7, hlam]
                                          · linarith only [h262, hlam, p237_0]
                                        · linarith only [h261, h3, hlam]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [h1, hlam, p237_1]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [h4, hlam, p237_1]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [hlam, p237_0]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [h2, h225, h231, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p237_1, u3elo0]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p237_1, u3elo0]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [h2, hlam, p237_0]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [h5, hlam, p237_0]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [h6, hlam, p237_0]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [hlam, p237_0]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [h8, hlam, p237_0]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [h3, hlam, p237_0]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [h0, h226, h231, h233, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p237_1]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [h7, hlam, p237_0]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [h2, h225, h231, h8, hc34, hlam, hphi, p237_1, u4elo4]
                                      · have p237_0 := h237c.1
                                        have p237_1 := h237c.2.1
                                        have p237_2 := h237c.2.2.1
                                        have p237_3 := h237c.2.2.2
                                        linarith only [hlam, p237_0]
                                · linarith only [h156, h226, h232, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                              · linarith only [h156, h225, h231, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                          · linarith only [h228, h7, hc13, hlam, hphi, u3elo0]
                        · linarith only [h156, h225, h227, hc24, hlam, hphi, u4elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h287 | h287
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h288 | h288
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h289 | h289
                            · linarith only [h2, h225, h226, h289, h3, h8, hc24, hlam, hphi, u4elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h291 | h291
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h292 | h292
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h293 | h293
                                  · linarith only [h225, h226, h292, h293, h4, h8, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h225, h226, h293, hc24, hlam, hphi, u4elo4]
                                · linarith only [h292, h7, hc23, hlam, hphi, u3elo0]
                              · linarith only [h156, h291, h6, hc13, hlam, hphi, u3elo0]
                          · linarith only [h156, h225, h288, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · linarith only [h156, h225, h287, hc24, hlam, hphi, u4elo3]
                    · linarith only [h225, h5, h8, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h301 | h301
                · linarith only [h301, h6, h7, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h303 | h303
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h304 | h304
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h305 | h305
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h307 | h307
                          · linarith only [h1, h307, h7, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h309 | h309
                            · linarith only [h2, h301, h309, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h311 | h311
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h312 | h312
                                · linarith only [h1, h303, h312, h7, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h314 | h314
                                  · linarith only [h2, h301, h304, h314, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h316 | h316
                                    · linarith only [h1, h301, h303, h311, h316, h7, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                    · linarith only [h316, h6, h7, hc34, hlam, hphi, u4elo4]
                              · linarith only [h1, h306, h311, h7, hc23, hlam, hphi, u3elo4]
                        · linarith only [h306, h6, h7, hc13, hlam, hphi, u3elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h321 | h321
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h322 | h322
                          · linarith only [h1, h322, h7, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h324 | h324
                            · linarith only [h2, h301, h324, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h326 | h326
                              · linarith only [h3, h301, h303, h305, h326, hc34, hlam, hphi, u4elo4]
                              · linarith only [h326, h6, h7, hc23, hlam, hphi, u3elo4]
                        · linarith only [h321, h6, h7, hc13, hlam, hphi, u3elo4]
                    · linarith only [h301, h304, h5, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · linarith only [h303, h4, h7, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h332 | h332
              · rcases m.htr 0 4 5 (by decide) (by decide) with h333 | h333
                · rcases m.htr 1 2 3 (by decide) (by decide) with h334 | h334
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h335 | h335
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h336 | h336
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h337 | h337
                        · linarith only [h1, h337, h6, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h339 | h339
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h340 | h340
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h341 | h341
                              · linarith only [h1, h334, h341, h6, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h343 | h343
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h344 | h344
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h345 | h345
                                    · rcases h0bigk with h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [hlam, p346_0]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h0, h335, h341, h343, h345, hc01, hc45, hlam, hphi, ht0b, ht5b, p346_1]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h1, h334, h343, h345, hc01, hc45, hlam, hphi, ht0b, ht5b, p346_1]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h1, h334, h343, h345, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p346_1]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        rcases p346_3 (m.d 0 1) (by simp) with h351 | h351
                                        · rcases p346_3 (m.d 0 2) (by simp) with h352 | h352
                                          · linarith only [h0, h352, hlam]
                                          · linarith only [h0, h335, h341, h343, h345, h352, hc01, hc45, hlam, hphi, ht0b, ht5b, p346_1]
                                        · linarith only [h3, h351, hlam]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h0, hlam, p346_0]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [hlam, p346_0]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h1, h334, h343, h345, hc02, hc45, hlam, hphi, ht0b, ht5b, p346_1]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h0, h1, h334, h343, h345, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p346_1]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        rcases p346_3 (m.d 0 1) (by simp) with h360 | h360
                                        · rcases p346_3 (m.d 0 2) (by simp) with h361 | h361
                                          · rcases p346_3 (m.d 0 3) (by simp) with h362 | h362
                                            · linarith only [h362, h4, hlam]
                                            · linarith only [h332, h362, hlam]
                                          · linarith only [h361, hlam, p346_0]
                                        · linarith only [h3, h360, hlam]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h1, hlam, p346_1]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h4, hlam, p346_1]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [hlam, p346_0]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h6, hlam, p346_1]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h6, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p346_1, u4elo3]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h2, hlam, p346_0]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h5, hlam, p346_0]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h1, h334, h343, hc04, hc35, hlam, hphi, ht0b, ht5b, p346_1]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [hlam, p346_0]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h3, h336, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p346_1, u4elo3]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h3, hlam, p346_0]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h3, h343, h345, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p346_1]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h332, hlam, p346_0]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [h333, hlam, p346_1]
                                      · have p346_0 := h346c.1
                                        have p346_1 := h346c.2.1
                                        have p346_2 := h346c.2.2.1
                                        have p346_3 := h346c.2.2.2
                                        linarith only [hlam, p346_0]
                                    · linarith only [h1, h334, h343, h345, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                                  · linarith only [h3, h332, h340, h341, h343, h344, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                                · linarith only [h332, h343, h6, hc23, hlam, hphi, ht34, u4elo3]
                            · linarith only [h333, h340, hc14, hlam, hphi, u4elo0]
                          · linarith only [h332, h339, h6, hc13, hlam, hphi, ht34, u4elo3]
                      · linarith only [h3, h332, h334, h336, h6, hc23, hlam, hphi, ht34, u4elo3]
                    · linarith only [h334, h335, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h334, h4, h6, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h332, h333, h6, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h391 | h391
                · rcases m.htr 1 2 3 (by decide) (by decide) with h392 | h392
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h393 | h393
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h394 | h394
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h395 | h395
                        · linarith only [h1, h395, h6, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h397 | h397
                          · linarith only [h332, h397, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h399 | h399
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h400 | h400
                              · linarith only [h1, h392, h400, h6, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h402 | h402
                                · linarith only [h1, h332, h392, h402, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h404 | h404
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h405 | h405
                                    · rcases h0bigk with h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [hlam, p406_0]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [h0, h393, h404, hc01, hc45, hlam, hphi, ht0b, ht5b, p406_1]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        rcases p406_3 (m.d 0 1) (by simp) with h409 | h409
                                        · rcases p406_3 (m.d 0 2) (by simp) with h410 | h410
                                          · linarith only [h0, h410, hlam]
                                          · linarith only [h4, h410, hlam]
                                        · linarith only [h1, h409, hlam]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [h2, h393, h404, hc01, hc45, hlam, hphi, ht0b, ht5b, p406_1]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        rcases p406_3 (m.d 0 1) (by simp) with h415 | h415
                                        · rcases p406_3 (m.d 0 2) (by simp) with h416 | h416
                                          · linarith only [h0, h416, hlam]
                                          · linarith only [h0, h393, h404, h416, hc01, hc45, hlam, hphi, ht0b, ht5b, p406_1]
                                        · linarith only [h3, h415, hlam]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [h0, hlam, p406_0]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [hlam, p406_0]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        rcases p406_3 (m.d 0 1) (by simp) with h422 | h422
                                        · rcases p406_3 (m.d 0 2) (by simp) with h423 | h423
                                          · rcases p406_3 (m.d 0 3) (by simp) with h424 | h424
                                            · linarith only [h4, h424, hlam]
                                            · rcases p406_3 (m.d 0 4) (by simp) with h426 | h426
                                              · linarith only [h426, h5, hlam]
                                              · linarith only [h426, h6, hlam]
                                          · linarith only [h4, h423, hlam]
                                        · linarith only [h1, h422, hlam]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [h2, h393, h404, hc02, hc45, hlam, hphi, ht0b, ht5b, p406_1]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        rcases p406_3 (m.d 0 1) (by simp) with h432 | h432
                                        · rcases p406_3 (m.d 0 2) (by simp) with h433 | h433
                                          · rcases p406_3 (m.d 0 3) (by simp) with h434 | h434
                                            · linarith only [h4, h434, hlam]
                                            · rcases p406_3 (m.d 0 4) (by simp) with h436 | h436
                                              · linarith only [h436, h5, hlam]
                                              · linarith only [h391, h436, hlam]
                                          · linarith only [h433, hlam, p406_0]
                                        · linarith only [h3, h432, hlam]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [h1, hlam, p406_1]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [h4, hlam, p406_1]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [hlam, p406_0]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [h6, hlam, p406_1]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [h332, hlam, p406_1]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [h2, hlam, p406_0]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [h5, hlam, p406_0]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [h1, h392, hc23, hlam, hphi, ht34, p406_1, u4elo0]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [hlam, p406_0]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [h1, h332, h392, h6, hc23, hlam, hphi, ht34, p406_1, u4elo3]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [h3, hlam, p406_0]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [h0, h393, h404, hc05, hc45, hlam, hphi, ht0b, ht5b, p406_1]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [h332, hc03, hlam, hphi, p406_1, u3elo4]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [h391, hlam, p406_1]
                                      · have p406_0 := h406c.1
                                        have p406_1 := h406c.2.1
                                        have p406_2 := h406c.2.2.1
                                        have p406_3 := h406c.2.2.2
                                        linarith only [hlam, p406_0]
                                    · linarith only [h393, h404, h405, h6, hc04, hlam, hphi, u4elo1]
                                  · linarith only [h2, h399, h400, h404, hc23, hlam, hphi, ht34, u4elo0]
                            · linarith only [h391, h399, h6, hc14, hlam, hphi, u4elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h459 | h459
                        · linarith only [h1, h459, h6, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h461 | h461
                          · linarith only [h1, h332, h461, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h463 | h463
                            · linarith only [h393, h394, h463, hlam]
                            · linarith only [h391, h463, hc14, hlam, hphi, u4elo0]
                    · linarith only [h392, h393, h5, h6, hc23, hlam, hphi, ht34, u4elo3]
                  · linarith only [h392, h4, h6, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h468 | h468
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h469 | h469
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h470 | h470
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h471 | h471
                        · linarith only [h1, h391, h471, h6, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h473 | h473
                          · linarith only [h1, h332, h473, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h475 | h475
                            · linarith only [h391, h475, h6, hc03, hlam, hphi, ht34, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h477 | h477
                              · linarith only [h1, h468, h477, h6, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h479 | h479
                                · linarith only [h1, h332, h468, h479, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h481 | h481
                                  · linarith only [h1, h391, h468, h481, h6, hc23, hlam, hphi, ht34, u4elo2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h483 | h483
                                    · linarith only [h1, h391, h468, h483, h6, hc23, hlam, hphi, u3elo3]
                                    · linarith only [h1, h468, h483, h6, hc23, hlam, hphi, ht34, u4elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h486 | h486
                        · linarith only [h1, h486, h6, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h488 | h488
                          · linarith only [h1, h332, h488, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h490 | h490
                            · linarith only [h2, h391, h490, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h492 | h492
                              · linarith only [h4, h492, h6, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h494 | h494
                                · linarith only [h3, h332, h469, h470, h492, h494, hlam]
                                · linarith only [h469, h470, h492, h494, hc23, hlam, hphi, u3elo4]
                    · linarith only [h391, h469, h5, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · linarith only [h391, h4, h468, h6, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h500 | h500
          · rcases m.htr 0 3 4 (by decide) (by decide) with h501 | h501
            · rcases m.htr 0 3 5 (by decide) (by decide) with h502 | h502
              · rcases m.htr 0 4 5 (by decide) (by decide) with h503 | h503
                · rcases m.htr 1 2 3 (by decide) (by decide) with h504 | h504
                  · linarith only [h0, h4, h500, h504, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h506 | h506
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h507 | h507
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h508 | h508
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h509 | h509
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h510 | h510
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h511 | h511
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h512 | h512
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h513 | h513
                                  · linarith only [h0, h4, h506, h513, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                  · linarith only [h2, h510, h511, h513, hc34, hlam, hphi, u4elo0]
                                · linarith only [h4, h512, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h4, h511, hc02, hlam, hphi, ht23, u3elo3]
                            · linarith only [h4, h500, h503, h508, h510, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                          · linarith only [h4, h502, h509, hc13, hlam, hphi, u3elo2]
                        · linarith only [h4, h501, h504, h508, hc12, hlam, hphi, ht23, u3elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h521 | h521
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h522 | h522
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h523 | h523
                            · linarith only [h506, h507, h523, hlam]
                            · linarith only [h4, h500, h503, h523, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                          · linarith only [h4, h502, h522, hc13, hlam, hphi, u3elo2]
                        · linarith only [h504, h506, h521, hc24, hlam, hphi, u4elo3]
                    · linarith only [h4, h500, h506, hc12, hlam, hphi, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h529 | h529
                  · linarith only [h0, h4, h500, h529, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h531 | h531
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h532 | h532
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h533 | h533
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h534 | h534
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h535 | h535
                            · linarith only [h503, h535, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h537 | h537
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h538 | h538
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h539 | h539
                                  · linarith only [h0, h4, h503, h531, h539, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h541 | h541
                                    · linarith only [h2, h503, h531, h537, h541, hlam]
                                    · rcases h0bigk with h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [hlam, p543_0]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [h0, h532, hc01, hc25, hlam, hphi, ht0b, ht5b, p543_1]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [h1, h529, h532, h538, hc01, hc35, hlam, hphi, ht0b, ht5b, p543_1]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        rcases p543_3 (m.d 0 1) (by simp) with h547 | h547
                                        · rcases p543_3 (m.d 0 2) (by simp) with h548 | h548
                                          · linarith only [h0, h548, hlam]
                                          · linarith only [h500, h548, hlam]
                                        · linarith only [h2, h547, hlam]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        rcases p543_3 (m.d 0 1) (by simp) with h552 | h552
                                        · rcases p543_3 (m.d 0 2) (by simp) with h553 | h553
                                          · linarith only [h0, h553, hlam]
                                          · linarith only [h0, h532, h537, h539, h553, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p543_1]
                                        · linarith only [h3, h552, hlam]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [h0, hlam, p543_0]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [hlam, p543_0]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [h4, hlam, p543_0]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [h2, h4, h531, h537, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p543_1, u3elo2]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p543_1, u3elo0]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [h1, hlam, p543_1]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [hc02, hlam, hphi, ht23, p543_1, u3elo0]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [hlam, p543_0]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [h2, h4, h531, h537, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p543_1, u3elo2]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [h3, h4, h531, h535, h537, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p543_1, u3elo2]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [h2, hlam, p543_0]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [h500, hlam, p543_0]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [h501, hlam, p543_0]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [hlam, p543_0]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [h503, hlam, p543_0]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [h3, hlam, p543_0]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [h0, h532, h537, h539, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p543_1]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [h502, hlam, p543_0]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [h2, h503, h531, h537, hc34, hlam, hphi, p543_1, u4elo4]
                                      · have p543_0 := h543c.1
                                        have p543_1 := h543c.2.1
                                        have p543_2 := h543c.2.2.1
                                        have p543_3 := h543c.2.2.2
                                        linarith only [hlam, p543_0]
                                · linarith only [h4, h538, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h0, h4, h531, h537, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                          · linarith only [h502, h529, h531, h534, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · linarith only [h529, h531, h533, hc24, hlam, hphi, u4elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h581 | h581
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h582 | h582
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h583 | h583
                            · linarith only [h2, h503, h583, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h585 | h585
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h586 | h586
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h587 | h587
                                  · linarith only [h2, h503, h531, h532, h587, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h531, h532, h585, h587, hc34, hlam, hphi, u4elo4]
                                · linarith only [h4, h586, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h4, h585, hc02, hlam, hphi, ht23, u3elo3]
                          · linarith only [h502, h582, hc13, hlam, hphi, u3elo0]
                        · linarith only [h529, h531, h581, hc24, hlam, hphi, u4elo3]
                    · linarith only [h4, h500, h531, hc12, hlam, hphi, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h595 | h595
                · linarith only [h4, h500, h502, h595, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h597 | h597
                  · linarith only [h0, h4, h502, h597, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h599 | h599
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h600 | h600
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h601 | h601
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h602 | h602
                          · linarith only [h0, h4, h502, h599, h602, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h597, h600, h602, hlam]
                        · linarith only [h501, h502, h597, h600, h601, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h606 | h606
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h607 | h607
                          · linarith only [h0, h4, h502, h599, h607, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h609 | h609
                            · linarith only [h2, h595, h609, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h611 | h611
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h612 | h612
                                · linarith only [h0, h4, h502, h599, h611, h612, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                · linarith only [h0, h4, h599, h611, h612, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                              · linarith only [h0, h4, h599, h611, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h501, h502, h606, hc13, hlam, hphi, u3elo4]
                    · linarith only [h4, h500, h599, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h4, h500, h501, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h619 | h619
            · rcases m.htr 0 3 5 (by decide) (by decide) with h620 | h620
              · rcases m.htr 0 4 5 (by decide) (by decide) with h621 | h621
                · rcases m.htr 1 2 3 (by decide) (by decide) with h622 | h622
                  · linarith only [h0, h500, h622, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h624 | h624
                    · linarith only [h500, h622, h624, hc02, hlam, hphi, ht23, u3elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h626 | h626
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h627 | h627
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h628 | h628
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h629 | h629
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h630 | h630
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h631 | h631
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h632 | h632
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h633 | h633
                                    · rcases h0bigk with h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [hlam, p634_0]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h0, h626, h631, h633, hc01, hc45, hlam, hphi, ht0b, ht5b, p634_1]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h1, h627, h633, hc01, hc45, hlam, hphi, ht0b, ht5b, p634_1]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h0, h500, h626, h631, h633, hc01, hc45, hlam, hphi, ht0b, ht5b, p634_1]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        rcases p634_3 (m.d 0 1) (by simp) with h639 | h639
                                        · rcases p634_3 (m.d 0 2) (by simp) with h640 | h640
                                          · linarith only [h0, h640, hlam]
                                          · linarith only [h0, h626, h631, h633, h640, hc01, hc45, hlam, hphi, ht0b, ht5b, p634_1]
                                        · linarith only [h3, h639, hlam]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h0, hlam, p634_0]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [hlam, p634_0]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h4, hlam, p634_0]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h500, hlam, p634_1]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h500, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p634_1, u4elo2]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h1, hlam, p634_1]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h0, h626, hc03, hc25, hlam, hphi, ht0b, ht5b, p634_1]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [hlam, p634_0]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h0, h4, h500, h626, h631, h633, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p634_1, u3elo2]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h3, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p634_1, u3elo2]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h2, hlam, p634_0]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h0, h626, h631, h633, hc04, hc45, hlam, hphi, ht0b, ht5b, p634_1]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h619, hlam, p634_0]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [hlam, p634_0]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h500, h620, h633, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p634_1, u4elo2]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h3, hlam, p634_0]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h0, h626, h631, h633, hc05, hc45, hlam, hphi, ht0b, ht5b, p634_1]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h620, hlam, p634_0]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [h621, hlam, p634_1]
                                      · have p634_0 := h634c.1
                                        have p634_1 := h634c.2.1
                                        have p634_2 := h634c.2.2.1
                                        have p634_3 := h634c.2.2.2
                                        linarith only [hlam, p634_0]
                                    · linarith only [h500, h621, h633, hc34, hlam, hphi, u4elo2]
                                  · linarith only [h3, h500, h621, h629, h632, hlam]
                                · linarith only [h4, h631, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h1, h4, h627, h630, hlam]
                            · linarith only [h621, h629, hc14, hlam, hphi, u4elo0]
                          · linarith only [h620, h627, h628, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · linarith only [h4, h619, h622, h627, hc12, hlam, hphi, ht23, u3elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h671 | h671
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h672 | h672
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h673 | h673
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h674 | h674
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h675 | h675
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h676 | h676
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h677 | h677
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
                                        rcases p678_3 (m.d 0 1) (by simp) with h680 | h680
                                        · rcases p678_3 (m.d 0 2) (by simp) with h681 | h681
                                          · linarith only [h0, h681, hlam]
                                          · rcases p678_3 (m.d 0 3) (by simp) with h683 | h683
                                            · linarith only [h1, h683, hlam]
                                            · linarith only [h4, h683, hlam]
                                        · linarith only [h0, h680, hlam]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h1, h671, h677, hc01, hc45, hlam, hphi, ht0b, ht5b, p678_1]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h619, h677, hc01, hc45, hlam, hphi, ht0b, ht5b, p678_1]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        rcases p678_3 (m.d 0 1) (by simp) with h689 | h689
                                        · rcases p678_3 (m.d 0 2) (by simp) with h690 | h690
                                          · linarith only [h0, h690, hlam]
                                          · rcases p678_3 (m.d 0 3) (by simp) with h692 | h692
                                            · linarith only [h1, h692, hlam]
                                            · linarith only [h620, h692, hlam]
                                        · linarith only [h3, h689, hlam]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h0, hlam, p678_0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [hlam, p678_0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h4, hlam, p678_0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h500, hlam, p678_1]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h3, h4, h626, hc12, hlam, hphi, ht23, p678_1, u3elo2]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h1, hlam, p678_1]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [hc02, hlam, hphi, ht23, p678_1, u3elo0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [hlam, p678_0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h2, h4, h671, h677, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p678_1, u3elo2]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h3, h4, h626, hc12, hlam, hphi, ht23, p678_1, u3elo2]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h2, hlam, p678_0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, p678_1, u4elo0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h619, hlam, p678_0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [hlam, p678_0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h3, h500, h626, hc12, hlam, hphi, ht23, ht34, p678_1, u4elo2]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h3, hlam, p678_0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h0, h4, h620, hc12, hlam, hphi, ht23, p678_1, u3elo2]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h620, hlam, p678_0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h621, hlam, p678_1]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [hlam, p678_0]
                                    · linarith only [h500, h621, h677, hc34, hlam, hphi, u4elo2]
                                  · linarith only [h0, h500, h676, hc12, hlam, hphi, ht23, ht34, u4elo4]
                                · linarith only [h4, h672, h675, hc03, hlam, hphi, u3elo1]
                              · linarith only [h0, h4, h674, hc12, hlam, hphi, ht23, u3elo3]
                            · linarith only [h500, h621, h673, hc14, hlam, hphi, u4elo2]
                          · linarith only [h4, h620, h672, hc13, hlam, hphi, u3elo2]
                        · linarith only [h4, h619, h622, h671, hc12, hlam, hphi, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h723 | h723
                  · linarith only [h0, h4, h723, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h725 | h725
                    · linarith only [h0, h500, h725, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h727 | h727
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h728 | h728
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h729 | h729
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h730 | h730
                            · linarith only [h500, h621, h730, hc02, hlam, hphi, ht23, ht34, u4elo1]
                            · linarith only [h725, h727, h730, hlam]
                          · linarith only [h620, h728, h729, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · linarith only [h4, h619, h723, h727, h728, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h735 | h735
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h736 | h736
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h737 | h737
                            · linarith only [h500, h621, h737, hc02, hlam, hphi, ht23, ht34, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h739 | h739
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h740 | h740
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h741 | h741
                                  · linarith only [h0, h500, h621, h741, hc12, hlam, hphi, ht23, ht34, u4elo2]
                                  · linarith only [h0, h500, h741, hc12, hlam, hphi, ht23, ht34, u4elo4]
                                · linarith only [h0, h4, h740, hc12, hlam, hphi, ht23, u3elo4]
                              · linarith only [h0, h4, h739, hc12, hlam, hphi, ht23, u3elo3]
                          · linarith only [h4, h620, h736, hc13, hlam, hphi, u3elo2]
                        · linarith only [h4, h619, h723, h735, hc12, hlam, hphi, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h748 | h748
                · linarith only [h619, h620, h748, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h750 | h750
                  · linarith only [h0, h500, h750, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h752 | h752
                    · linarith only [h0, h500, h748, h752, hc24, hlam, hphi, u4elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h754 | h754
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h755 | h755
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h756 | h756
                          · linarith only [h1, h620, h756, hlam]
                          · linarith only [h0, h500, h748, h754, h755, h756, hc34, hlam, hphi, u4elo4]
                        · linarith only [h619, h620, h755, hc13, hlam, hphi, u3elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h760 | h760
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h761 | h761
                          · linarith only [h620, h761, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h763 | h763
                            · linarith only [h2, h748, h763, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h765 | h765
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h766 | h766
                                · linarith only [h1, h620, h760, h766, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                · linarith only [h0, h4, h766, hc12, hlam, hphi, ht23, u3elo4]
                              · linarith only [h0, h4, h765, hc12, hlam, hphi, ht23, u3elo3]
                        · linarith only [h619, h620, h760, hc13, hlam, hphi, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h771 | h771
              · rcases m.htr 0 4 5 (by decide) (by decide) with h772 | h772
                · rcases m.htr 1 2 3 (by decide) (by decide) with h773 | h773
                  · linarith only [h0, h500, h773, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h775 | h775
                    · linarith only [h500, h773, h775, hc02, hlam, hphi, ht23, u3elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h777 | h777
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h778 | h778
                        · linarith only [h1, h619, h778, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h780 | h780
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h781 | h781
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h782 | h782
                              · linarith only [h619, h782, hc03, hlam, hphi, u3elo2]
                              · linarith only [h0, h4, h777, h782, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                            · linarith only [h772, h781, hc14, hlam, hphi, u4elo0]
                          · linarith only [h619, h771, h780, hc13, hlam, hphi, ht34, u4elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h787 | h787
                        · linarith only [h619, h787, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h789 | h789
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h790 | h790
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h791 | h791
                              · linarith only [h1, h619, h789, h791, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                              · linarith only [h0, h4, h791, hc12, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h772, h787, h789, h790, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                          · linarith only [h619, h771, h789, hc13, hlam, hphi, ht34, u4elo3]
                · linarith only [h619, h771, h772, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h797 | h797
                · rcases m.htr 1 2 3 (by decide) (by decide) with h798 | h798
                  · linarith only [h0, h4, h771, h798, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h800 | h800
                    · linarith only [h0, h4, h619, h800, hc24, hlam, hphi, u4elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h802 | h802
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h803 | h803
                        · linarith only [h1, h619, h803, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h805 | h805
                          · linarith only [h0, h4, h771, h802, h805, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h798, h802, h805, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h808 | h808
                        · linarith only [h4, h619, h808, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h810 | h810
                          · linarith only [h1, h771, h810, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h812 | h812
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h813 | h813
                              · linarith only [h0, h4, h619, h813, hc12, hlam, hphi, ht23, u3elo2]
                              · linarith only [h0, h4, h813, hc12, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h797, h812, hc14, hlam, hphi, u4elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h817 | h817
                  · linarith only [h0, h4, h817, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h819 | h819
                    · linarith only [h0, h500, h819, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h821 | h821
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h822 | h822
                        · linarith only [h1, h619, h797, h822, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h824 | h824
                          · linarith only [h1, h771, h824, hlam]
                          · linarith only [h817, h821, h824, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h827 | h827
                        · linarith only [h4, h619, h827, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h829 | h829
                          · linarith only [h1, h771, h829, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h831 | h831
                            · linarith only [h0, h4, h619, h797, h831, hc12, hlam, hphi, ht23, ht34, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h833 | h833
                              · linarith only [h0, h4, h619, h833, hc12, hlam, hphi, ht23, u3elo2]
                              · linarith only [h0, h4, h833, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h836 | h836
        · rcases m.htr 0 2 4 (by decide) (by decide) with h837 | h837
          · rcases m.htr 0 3 4 (by decide) (by decide) with h838 | h838
            · rcases m.htr 0 3 5 (by decide) (by decide) with h839 | h839
              · linarith only [h1, h3, h839, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h841 | h841
                · linarith only [h2, h3, h841, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h843 | h843
                  · linarith only [h0, h3, h839, h843, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h3, h836, h841, h843, hc12, hlam, hphi, ht23, ht34, u4elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h846 | h846
              · linarith only [h1, h3, h846, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h848 | h848
                · linarith only [h0, h3, h837, h848, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h850 | h850
                  · linarith only [h0, h3, h848, h850, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h836, h838, h850, hc12, hlam, hphi, ht23, u3elo3]
          · linarith only [h836, h837, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h854 | h854
          · rcases m.htr 0 3 4 (by decide) (by decide) with h855 | h855
            · rcases m.htr 0 3 5 (by decide) (by decide) with h856 | h856
              · linarith only [h1, h3, h856, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h858 | h858
                · linarith only [h2, h3, h858, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h860 | h860
                  · linarith only [h0, h3, h836, h854, h858, h860, hc24, hlam, hphi, u4elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h862 | h862
                    · linarith only [h0, h3, h858, h862, hc24, hlam, hphi, u4elo4]
                    · linarith only [h836, h854, h856, h862, hc12, hlam, hphi, ht23, u3elo4]
            · linarith only [h836, h854, h855, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h866 | h866
            · rcases m.htr 0 3 5 (by decide) (by decide) with h867 | h867
              · linarith only [h1, h3, h867, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h869 | h869
                · linarith only [h1, h3, h866, h867, h869, hc13, hlam, hphi, u3elo4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h871 | h871
                  · linarith only [h0, h836, h871, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h873 | h873
                    · linarith only [h0, h3, h869, h873, hc24, hlam, hphi, u4elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h875 | h875
                      · linarith only [h1, h3, h871, h875, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h877 | h877
                        · linarith only [h1, h3, h869, h877, hc34, hlam, hphi, u4elo4]
                        · linarith only [h866, h867, h871, h877, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h880 | h880
              · linarith only [h2, h3, h866, h880, hc14, hlam, hphi, u4elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h882 | h882
                · linarith only [h2, h3, h882, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h884 | h884
                  · linarith only [h0, h854, h884, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h886 | h886
                    · linarith only [h0, h854, h886, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h888 | h888
                      · linarith only [h1, h3, h884, h888, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h890 | h890
                        · linarith only [h1, h866, h882, h890, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h892 | h892
                          · linarith only [h836, h880, h892, hc02, hlam, hphi, ht23, u3elo1]
                          · linarith only [h0, h3, h892, hc12, hlam, hphi, ht23, u3elo4]
    · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

end R2N4
