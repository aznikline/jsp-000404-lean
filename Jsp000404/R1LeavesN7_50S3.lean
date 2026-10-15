import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_50S1
import Jsp000404.R1LeavesN7_50S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5456000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_M_IR_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_M_IR_x1 m hb0 hb2 hb3 hb5 h0

set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
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
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                                  · linarith only [h0, h10, h17, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                  · linarith only [h0, h10, h14, h16, h17, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h0, h10, h13, h16, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                                  · linarith only [h0, h10, h22, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                  · linarith only [h0, h10, h14, h21, h22, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · linarith only [h0, h10, h13, h21, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                              · linarith only [h0, h13, h14, h26, h4, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
                                  · linarith only [h10, h14, h29, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
                                    · linarith only [h11, h26, h31, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h33 | h33
                                      · linarith only [h0, h10, h11, h14, h26, h28, h33, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                      · rcases h1bigk with h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h12, hc01, hlam, hphi, ht0b, ht5b, p35_1, u5ehi2]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          rcases p35_3 (m.d 0 1) (by simp) with h38 | h38
                                          · rcases p35_3 (m.d 1 2) (by simp) with h39 | h39
                                            · linarith only [h0, h39, hlam]
                                            · linarith only [h10, h39, hlam]
                                          · linarith only [h38, hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          rcases p35_3 (m.d 0 1) (by simp) with h43 | h43
                                          · rcases p35_3 (m.d 1 2) (by simp) with h44 | h44
                                            · linarith only [h0, h44, hlam]
                                            · linarith only [h11, h44, hlam]
                                          · linarith only [h43, hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          rcases p35_3 (m.d 0 1) (by simp) with h48 | h48
                                          · rcases p35_3 (m.d 1 2) (by simp) with h49 | h49
                                            · linarith only [h0, h49, hlam]
                                            · linarith only [h12, h49, hlam]
                                          · linarith only [h48, hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h0, hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h0, h10, h28, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p35_1]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h0, h11, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p35_1, u2ehi3]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p35_1, u5ehi1]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h1, hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h10, hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h1, h11, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p35_1, u2ehi3]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h14, hlam, p35_1]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h2, hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h11, hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h13, hlam, p35_1]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h26, hlam, p35_1]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h3, hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h12, hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h10, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p35_1, u2ehi2]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h0, h11, h14, h33, h4, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p35_1, u2ehi3]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [hlam, p35_0]
                                · linarith only [h1, h13, h28, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                            · linarith only [h0, h13, h4, h7, h74, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                                · linarith only [h0, h10, h13, h77, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h79 | h79
                                  · linarith only [h0, h10, h13, h4, h7, h79, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h81 | h81
                                    · linarith only [h0, h11, h81, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · linarith only [h2, h76, h81, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                                · linarith only [h10, h13, h84, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h86 | h86
                                  · linarith only [h10, h74, h86, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h88 | h88
                                    · linarith only [h10, h13, h76, h88, hc24, hlam, hphi, u2ehi2]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h90 | h90
                                      · linarith only [h10, h13, h76, h90, hc34, hlam, hphi, ht23, u2ehi2]
                                      · linarith only [h0, h10, h13, h4, h7, h9, h90, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h10, h12, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h10, h11, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
                      · linarith only [h10, h95, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h97 | h97
                        · linarith only [h0, h10, h4, h97, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h100 | h100
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h101 | h101
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h102 | h102
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h103 | h103
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h104 | h104
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h105 | h105
                                      · linarith only [h1, h105, h99, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                      · rcases h1bigk with h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          rcases p107_3 (m.d 0 1) (by simp) with h109 | h109
                                          · rcases p107_3 (m.d 1 2) (by simp) with h110 | h110
                                            · linarith only [h110, hlam, p107_0]
                                            · rcases p107_3 (m.d 1 3) (by simp) with h112 | h112
                                              · linarith only [h1, h112, hlam]
                                              · linarith only [h10, h112, hlam]
                                          · linarith only [h109, hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h101, h105, h99, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p107_1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h101, h105, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p107_1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          rcases p107_3 (m.d 0 1) (by simp) with h118 | h118
                                          · rcases p107_3 (m.d 1 2) (by simp) with h119 | h119
                                            · linarith only [h0, h119, hlam]
                                            · rcases p107_3 (m.d 1 3) (by simp) with h121 | h121
                                              · linarith only [h1, h121, hlam]
                                              · linarith only [h100, h121, hlam]
                                          · linarith only [h118, hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h0, hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h10, hlam, p107_1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h95, hlam, p107_1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h97, hlam, p107_1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h1, hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h1, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p107_1, u2ehi1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h0, h10, h101, h105, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p107_1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h0, h10, h4, h97, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p107_1, u2ehi1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h2, hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p107_1, u2ehi1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h99, hlam, p107_1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h0, h102, h4, h95, h97, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p107_1, u2ehi1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h3, hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p107_1, u2ehi1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h100, hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h101, hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [hlam, p107_0]
                                    · linarith only [h0, h104, h4, h7, h9, h95, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                  · linarith only [h0, h10, h103, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h0, h10, h101, h102, h4, h7, h99, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h148 | h148
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h149 | h149
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h150 | h150
                                    · linarith only [h101, h150, h95, hc24, hlam, hphi, u2ehi1]
                                    · linarith only [h0, h150, h4, h7, h9, h95, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                  · linarith only [h10, h100, h149, hlam]
                                · linarith only [h0, h10, h100, h148, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h155 | h155
                              · linarith only [h0, h100, h155, h4, h8, h99, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h157 | h157
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h158 | h158
                                  · linarith only [h0, h100, h158, h4, h99, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h0, h10, h158, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h10, h157, hc34, hlam, hphi, ht23, u2ehi1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
                            · linarith only [h0, h162, h4, h7, h99, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h164 | h164
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                                · linarith only [h0, h10, h165, h4, h99, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h0, h10, h165, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h168 | h168
                                · linarith only [h10, h168, h99, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h10, h168, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h171 | h171
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h172 | h172
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h173 | h173
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h174 | h174
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h175 | h175
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h176 | h176
                              · linarith only [h176, h2, h9, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h178 | h178
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h179 | h179
                                  · linarith only [h0, h171, h179, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                  · linarith only [h1, h175, h179, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h178, h7, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h183 | h183
                              · linarith only [h183, h2, h9, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h185 | h185
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h186 | h186
                                  · linarith only [h172, h174, h175, h186, hc23, hlam, hphi, u2ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h188 | h188
                                    · linarith only [h172, h174, h175, h188, h8, h9, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h190 | h190
                                      · linarith only [h172, h174, h175, h190, h8, h9, hc34, hlam, hphi, ht23, u2ehi3]
                                      · rcases h1bigk with h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [hlam, p192_0]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [h173, hc01, hlam, hphi, ht0b, ht5b, p192_1, u5ehi2]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          rcases p192_3 (m.d 0 1) (by simp) with h195 | h195
                                          · rcases p192_3 (m.d 1 2) (by simp) with h196 | h196
                                            · linarith only [h0, h196, hlam]
                                            · linarith only [h171, h196, hlam]
                                          · linarith only [h195, hlam, p192_0]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          rcases p192_3 (m.d 0 1) (by simp) with h200 | h200
                                          · rcases p192_3 (m.d 1 2) (by simp) with h201 | h201
                                            · linarith only [h0, h201, hlam]
                                            · linarith only [h172, h201, hlam]
                                          · linarith only [h200, hlam, p192_0]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          rcases p192_3 (m.d 0 1) (by simp) with h205 | h205
                                          · rcases p192_3 (m.d 1 2) (by simp) with h206 | h206
                                            · linarith only [h0, h206, hlam]
                                            · linarith only [h173, h206, hlam]
                                          · linarith only [h205, hlam, p192_0]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [h0, hlam, p192_0]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [hlam, p192_0]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [h0, h172, h174, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p192_1, u2ehi3]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [h0, h172, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p192_1, u2ehi3]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p192_1, u5ehi1]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [h1, hlam, p192_0]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [h171, hlam, p192_0]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [hlam, p192_0]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [h172, h175, h8, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p192_1, u2ehi3]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [h175, hlam, p192_1]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [h2, hlam, p192_0]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [h172, hlam, p192_0]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [h174, hlam, p192_1]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [hlam, p192_0]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [h183, hlam, p192_1]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [h3, hlam, p192_0]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [h173, hlam, p192_0]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [h172, h174, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p192_1, u2ehi3]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [h0, h172, h175, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p192_1, u2ehi3]
                                        · have p192_0 := h192c.1
                                          have p192_1 := h192c.2.1
                                          have p192_2 := h192c.2.2.1
                                          have p192_3 := h192c.2.2.2
                                          linarith only [hlam, p192_0]
                                · linarith only [h185, h7, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h171, h174, h7, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h171, h173, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h171, h172, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h234 | h234
                      · linarith only [h171, h234, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h234, h5, h9, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h237 | h237
                  · linarith only [h237, h7, h8, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h239 | h239
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h240 | h240
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h241 | h241
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h242 | h242
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h243 | h243
                            · linarith only [h1, h243, h8, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h245 | h245
                              · linarith only [h2, h237, h245, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h247 | h247
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h248 | h248
                                  · linarith only [h0, h239, h248, h8, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h250 | h250
                                    · linarith only [h2, h237, h240, h250, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h252 | h252
                                      · linarith only [h0, h2, h237, h240, h241, h247, h248, h252, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                      · rcases h1bigk with h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [hlam, p254_0]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [h241, hc01, hlam, hphi, ht0b, ht5b, p254_1, u5ehi2]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          rcases p254_3 (m.d 0 1) (by simp) with h257 | h257
                                          · rcases p254_3 (m.d 1 2) (by simp) with h258 | h258
                                            · linarith only [h0, h258, hlam]
                                            · linarith only [h239, h258, hlam]
                                          · linarith only [h257, hlam, p254_0]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          rcases p254_3 (m.d 0 1) (by simp) with h262 | h262
                                          · rcases p254_3 (m.d 1 2) (by simp) with h263 | h263
                                            · linarith only [h0, h263, hlam]
                                            · linarith only [h240, h263, hlam]
                                          · linarith only [h262, hlam, p254_0]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          rcases p254_3 (m.d 0 1) (by simp) with h267 | h267
                                          · rcases p254_3 (m.d 1 2) (by simp) with h268 | h268
                                            · linarith only [h0, h268, hlam]
                                            · linarith only [h241, h268, hlam]
                                          · linarith only [h267, hlam, p254_0]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [h0, hlam, p254_0]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [hlam, p254_0]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [h0, h240, h242, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p254_1, u2ehi3]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [h0, h240, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p254_1, u2ehi3]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [h0, h240, h242, h243, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p254_1, u2ehi3]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [h1, hlam, p254_0]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [h239, hlam, p254_0]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [hlam, p254_0]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [h1, h240, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p254_1, u2ehi3]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [h243, hlam, p254_1]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [h2, hlam, p254_0]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [h240, hlam, p254_0]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [h242, hlam, p254_1]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [hlam, p254_0]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [h245, hlam, p254_1]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [h3, hlam, p254_0]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [h241, hlam, p254_0]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [h239, h247, h252, h3, h8, hc45, hlam, hphi, ht23, ht34, p254_1, u2ehi3]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [h240, h252, h3, h8, hc45, hlam, hphi, ht23, ht34, p254_1, u2ehi3]
                                        · have p254_0 := h254c.1
                                          have p254_1 := h254c.2.1
                                          have p254_2 := h254c.2.2.1
                                          have p254_3 := h254c.2.2.2
                                          linarith only [hlam, p254_0]
                                · linarith only [h247, h7, h8, hc23, hc35, hlam, hphi]
                          · linarith only [h239, h242, h7, h8, hc35, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h0, h239, h241, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h239, h240, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h239, h4, h8, hc35, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h297 | h297
                · rcases m.htr 0 4 5 (by decide) (by decide) with h298 | h298
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h299 | h299
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h300 | h300
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h301 | h301
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h302 | h302
                          · linarith only [h297, h302, h7, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h304 | h304
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h305 | h305
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h306 | h306
                                · linarith only [h1, h304, h306, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h308 | h308
                                  · linarith only [h0, h300, h306, h308, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                  · linarith only [h1, h304, h308, h7, hc23, hc34, hlam, hphi]
                              · linarith only [h298, h302, h304, h305, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h297, h304, h7, hc13, hc34, hlam, hphi]
                        · linarith only [h300, h301, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h299, h300, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h299, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h297, h298, h7, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h317 | h317
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h318 | h318
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h319 | h319
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h320 | h320
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h321 | h321
                          · linarith only [h1, h321, h7, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h323 | h323
                            · linarith only [h1, h297, h323, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h325 | h325
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h326 | h326
                                · linarith only [h1, h318, h326, h7, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h328 | h328
                                  · linarith only [h1, h297, h318, h328, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h330 | h330
                                    · linarith only [h0, h319, h330, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · linarith only [h2, h325, h330, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h317, h319, h325, h7, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h318, h320, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h318, h319, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h318, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h337 | h337
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h338 | h338
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h339 | h339
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h340 | h340
                          · linarith only [h1, h340, h7, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h342 | h342
                            · linarith only [h1, h297, h317, h342, h6, h7, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h344 | h344
                              · linarith only [h2, h317, h344, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h346 | h346
                                · linarith only [h1, h337, h346, h7, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h348 | h348
                                  · linarith only [h1, h297, h337, h348, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h350 | h350
                                    · linarith only [h0, h317, h338, h350, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h352 | h352
                                      · linarith only [h1, h317, h337, h352, h7, hc34, hlam, hphi, ht23, u2ehi2]
                                      · linarith only [h1, h337, h352, h7, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h337, h339, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h337, h338, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h337, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
            · linarith only [h4, h6, hc25, hlam, hphi, u2ehi2]
          · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h360 | h360
          · linarith only [h360, h4, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h362 | h362
            · linarith only [h362, h4, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h364 | h364
              · rcases m.htr 0 3 5 (by decide) (by decide) with h365 | h365
                · rcases m.htr 0 4 5 (by decide) (by decide) with h366 | h366
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h367 | h367
                    · linarith only [h0, h367, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h369 | h369
                      · linarith only [h0, h360, h369, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h371 | h371
                        · linarith only [h0, h362, h371, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h373 | h373
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h375 | h375
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h376 | h376
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h377 | h377
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h378 | h378
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h379 | h379
                                      · linarith only [h1, h373, h379, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                      · rcases h1bigk with h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [hlam, p381_0]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          rcases p381_3 (m.d 0 1) (by simp) with h383 | h383
                                          · rcases p381_3 (m.d 1 2) (by simp) with h384 | h384
                                            · linarith only [h384, hlam, p381_0]
                                            · rcases p381_3 (m.d 1 3) (by simp) with h386 | h386
                                              · linarith only [h1, h386, hlam]
                                              · linarith only [h367, h386, hlam]
                                          · linarith only [h383, hlam, p381_0]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h373, h375, h379, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p381_1]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h375, h379, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p381_1]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          rcases p381_3 (m.d 0 1) (by simp) with h392 | h392
                                          · rcases p381_3 (m.d 1 2) (by simp) with h393 | h393
                                            · linarith only [h0, h393, hlam]
                                            · rcases p381_3 (m.d 1 3) (by simp) with h395 | h395
                                              · linarith only [h1, h395, hlam]
                                              · linarith only [h374, h395, hlam]
                                          · linarith only [h392, hlam, p381_0]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h0, hlam, p381_0]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [hlam, p381_0]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h367, hlam, p381_1]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h369, hlam, p381_1]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h371, hlam, p381_1]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h1, hlam, p381_0]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h1, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p381_1, u2ehi1]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [hlam, p381_0]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h1, h375, h379, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p381_1]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p381_1, u5ehi1]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h2, hlam, p381_0]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p381_1, u2ehi1]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h373, hlam, p381_1]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [hlam, p381_0]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h2, h360, h371, h376, hc23, hlam, hphi, p381_1, u2ehi1]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h3, hlam, p381_0]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p381_1, u2ehi1]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h374, hlam, p381_0]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [h375, hlam, p381_0]
                                        · have p381_0 := h381c.1
                                          have p381_1 := h381c.2.1
                                          have p381_2 := h381c.2.2.1
                                          have p381_3 := h381c.2.2.2
                                          linarith only [hlam, p381_0]
                                    · linarith only [h360, h378, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                                  · linarith only [h0, h377, h4, hc35, hlam, hphi, ht23, u2ehi1]
                                · linarith only [h0, h376, h4, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h364, h366, h369, h375, h4, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h365, h367, h374, h4, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h364, h367, h373, h4, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h425 | h425
                    · linarith only [h0, h365, h4, h425, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h427 | h427
                      · linarith only [h0, h360, h366, h427, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h429 | h429
                        · linarith only [h0, h360, h366, h429, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h431 | h431
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h432 | h432
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h433 | h433
                              · linarith only [h1, h360, h366, h431, h433, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h435 | h435
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h436 | h436
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h437 | h437
                                    · linarith only [h0, h360, h366, h437, hc24, hlam, hphi, u2ehi1]
                                    · linarith only [h0, h360, h437, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                  · linarith only [h0, h4, h436, hc35, hlam, hphi, ht23, u2ehi1]
                                · linarith only [h1, h2, h4, h431, h432, h435, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h365, h4, h425, h432, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h364, h4, h425, h431, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h444 | h444
                  · linarith only [h364, h365, h444, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h446 | h446
                    · linarith only [h0, h360, h446, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h448 | h448
                      · linarith only [h0, h4, h448, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h450 | h450
                        · linarith only [h0, h360, h444, h450, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h452 | h452
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h453 | h453
                            · linarith only [h1, h365, h453, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h455 | h455
                              · linarith only [h1, h360, h444, h452, h455, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h457 | h457
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h458 | h458
                                  · linarith only [h0, h365, h4, h458, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h0, h4, h458, hc35, hlam, hphi, ht23, u2ehi1]
                                · linarith only [h0, h4, h457, hc34, hlam, hphi, ht23, u2ehi1]
                          · linarith only [h364, h365, h452, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h463 | h463
                · rcases m.htr 0 4 5 (by decide) (by decide) with h464 | h464
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h465 | h465
                    · linarith only [h0, h4, h465, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h467 | h467
                      · linarith only [h0, h360, h467, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h469 | h469
                        · linarith only [h0, h362, h469, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h471 | h471
                          · linarith only [h364, h463, h471, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h473 | h473
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h474 | h474
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h475 | h475
                                · linarith only [h1, h364, h473, h475, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                                · linarith only [h4, h475, hc34, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h364, h463, h464, h467, h474, hc34, hlam, hphi, ht23, u2ehi1]
                            · linarith only [h364, h463, h473, hc13, hc34, hlam, hphi]
                  · linarith only [h364, h463, h464, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h481 | h481
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h482 | h482
                    · linarith only [h0, h4, h482, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h484 | h484
                      · linarith only [h0, h4, h484, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h486 | h486
                        · linarith only [h1, h463, h482, h486, hc35, hlam, hphi, ht23, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h488 | h488
                          · linarith only [h1, h364, h488, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h490 | h490
                            · linarith only [h1, h463, h490, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h492 | h492
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h493 | h493
                                · linarith only [h364, h4, h493, hc23, hlam, hphi, u2ehi0]
                                · linarith only [h4, h493, hc34, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h360, h481, h484, h492, hc24, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h497 | h497
                    · linarith only [h0, h4, h497, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h499 | h499
                      · linarith only [h0, h4, h499, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h501 | h501
                        · linarith only [h0, h362, h501, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h503 | h503
                          · linarith only [h1, h364, h503, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h505 | h505
                            · linarith only [h1, h463, h505, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h507 | h507
                              · linarith only [h2, h481, h507, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h509 | h509
                                · linarith only [h364, h4, h509, hc23, hlam, hphi, u2ehi0]
                                · linarith only [h0, h4, h509, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h512 | h512
        · rcases m.htr 0 2 4 (by decide) (by decide) with h513 | h513
          · rcases m.htr 0 2 5 (by decide) (by decide) with h514 | h514
            · linarith only [h0, h3, h514, hlam]
            · linarith only [h512, h514, hc25, hlam, hphi, u2ehi2]
          · linarith only [h512, h513, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h518 | h518
          · linarith only [h512, h518, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h520 | h520
            · linarith only [h512, h520, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h522 | h522
              · rcases m.htr 0 3 5 (by decide) (by decide) with h523 | h523
                · linarith only [h1, h3, h523, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h525 | h525
                  · linarith only [h0, h3, h522, h523, h525, hc35, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h527 | h527
                    · linarith only [h0, h518, h522, h523, h527, hc35, hlam, hphi, ht23, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h529 | h529
                      · linarith only [h1, h3, h518, h527, h529, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h531 | h531
                        · linarith only [h0, h512, h531, hc23, hlam, hphi, u2ehi4]
                        · linarith only [h1, h3, h527, h531, hc25, hlam, hphi, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h534 | h534
                · linarith only [h0, h3, h522, h534, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h536 | h536
                  · linarith only [h2, h3, h536, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h538 | h538
                    · linarith only [h0, h3, h538, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h540 | h540
                      · linarith only [h0, h518, h540, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h542 | h542
                        · linarith only [h0, h3, h542, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                        · linarith only [h1, h3, h538, h542, hc25, hlam, hphi, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h545 | h545
      · rcases m.htr 0 2 3 (by decide) (by decide) with h546 | h546
        · rcases m.htr 0 2 4 (by decide) (by decide) with h547 | h547
          · linarith only [h0, h2, h547, hlam]
          · linarith only [h546, h547, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h550 | h550
          · linarith only [h546, h550, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h552 | h552
            · linarith only [h546, h552, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h554 | h554
              · linarith only [h1, h2, h554, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h556 | h556
                · rcases m.htr 0 4 5 (by decide) (by decide) with h557 | h557
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h558 | h558
                    · linarith only [h0, h546, h558, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h560 | h560
                      · linarith only [h0, h546, h560, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h1, h2, h558, h560, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h557, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h564 | h564
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h565 | h565
                    · linarith only [h0, h546, h565, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h567 | h567
                      · linarith only [h0, h546, h567, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h1, h2, h565, h567, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h564, hc45, hlam, hphi, ht23, ht34, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h571 | h571
        · rcases m.htr 0 2 4 (by decide) (by decide) with h572 | h572
          · linarith only [h0, h2, h572, hlam]
          · linarith only [h571, h572, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h575 | h575
          · linarith only [h571, h575, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h577 | h577
            · linarith only [h571, h577, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h579 | h579
              · linarith only [h1, h2, h579, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h581 | h581
                · linarith only [h0, h545, h579, h581, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h583 | h583
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h584 | h584
                    · linarith only [h0, h2, h584, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h586 | h586
                      · linarith only [h0, h571, h575, h583, h586, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h1, h2, h584, h586, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h583, hc45, hlam, hphi, ht23, ht34, u2ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h590 | h590
    · rcases m.htr 0 1 5 (by decide) (by decide) with h591 | h591
      · rcases m.htr 0 2 3 (by decide) (by decide) with h592 | h592
        · linarith only [h0, h1, h592, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h594 | h594
          · linarith only [h592, h594, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h596 | h596
            · linarith only [h592, h596, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h598 | h598
              · rcases m.htr 0 3 5 (by decide) (by decide) with h599 | h599
                · rcases m.htr 0 4 5 (by decide) (by decide) with h600 | h600
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h601 | h601
                    · linarith only [h0, h1, h601, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h601, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h604 | h604
                    · linarith only [h0, h1, h604, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h604, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h599, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h598, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h609 | h609
        · linarith only [h0, h1, h609, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h611 | h611
          · linarith only [h609, h611, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h613 | h613
            · linarith only [h609, h613, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h615 | h615
              · rcases m.htr 0 3 5 (by decide) (by decide) with h616 | h616
                · rcases m.htr 0 4 5 (by decide) (by decide) with h617 | h617
                  · linarith only [h590, h591, h617, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h619 | h619
                    · linarith only [h0, h1, h619, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h619, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h616, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h615, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h624 | h624
      · rcases m.htr 0 2 3 (by decide) (by decide) with h625 | h625
        · linarith only [h0, h1, h625, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h627 | h627
          · linarith only [h625, h627, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h629 | h629
            · linarith only [h625, h629, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h631 | h631
              · rcases m.htr 0 3 5 (by decide) (by decide) with h632 | h632
                · rcases m.htr 0 4 5 (by decide) (by decide) with h633 | h633
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h634 | h634
                    · linarith only [h0, h1, h634, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h634, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h590, h633, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h590, h631, h632, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h631, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h640 | h640
        · linarith only [h0, h1, h640, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h642 | h642
          · linarith only [h640, h642, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h644 | h644
            · linarith only [h640, h644, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h646 | h646
              · rcases m.htr 0 3 5 (by decide) (by decide) with h647 | h647
                · rcases m.htr 0 4 5 (by decide) (by decide) with h648 | h648
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h649 | h649
                    · linarith only [h0, h1, h640, h649, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h649, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h590, h648, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h590, h646, h647, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h646, hc34, hlam, hphi, ht23, u2ehi1]

set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h655 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h656 | h656
  · rcases m.htr 0 1 5 (by decide) (by decide) with h657 | h657
    · rcases m.htr 0 2 3 (by decide) (by decide) with h658 | h658
      · rcases m.htr 0 2 4 (by decide) (by decide) with h659 | h659
        · rcases m.htr 0 2 5 (by decide) (by decide) with h660 | h660
          · rcases m.htr 0 3 4 (by decide) (by decide) with h661 | h661
            · rcases m.htr 0 3 5 (by decide) (by decide) with h662 | h662
              · rcases m.htr 0 4 5 (by decide) (by decide) with h663 | h663
                · rcases m.htr 1 2 3 (by decide) (by decide) with h664 | h664
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h665 | h665
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h666 | h666
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h667 | h667
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h668 | h668
                          · linarith only [h0, h655, h668, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h0, h655, h662, h667, h668, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h655, h661, h664, h667, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h657, h666, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h657, h665, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h655, h661, h663, h664, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h675 | h675
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h676 | h676
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h677 | h677
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h678 | h678
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h679 | h679
                          · linarith only [h0, h655, h679, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h0, h655, h662, h676, h678, h679, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h0, h655, h661, h675, h678, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h657, h677, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h659, h663, h676, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h655, h662, h675, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h686 | h686
                · linarith only [h661, h662, h686, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h688 | h688
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h689 | h689
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h690 | h690
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h691 | h691
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h692 | h692
                          · linarith only [h0, h655, h662, h692, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h694 | h694
                            · linarith only [h0, h657, h686, h691, h692, h694, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h696 | h696
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h697 | h697
                                · linarith only [h655, h662, h688, h697, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h699 | h699
                                  · linarith only [h656, h686, h689, h699, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h701 | h701
                                    · linarith only [h0, h656, h657, h686, h688, h689, h692, h696, h701, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · rcases h1bigk with h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [hlam, p703_0]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [h0, hlam, p703_0]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [h0, h688, h696, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p703_1]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [h0, h689, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p703_1, u2ehi3]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p703_1, u5ehi1]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [h655, h688, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p703_1, u2ehi2]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [hlam, p703_0]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        rcases p703_3 (m.d 0 1) (by simp) with h711 | h711
                                        · linarith only [h0, h711, hlam]
                                        · linarith only [h655, h711, hlam]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        rcases p703_3 (m.d 0 1) (by simp) with h714 | h714
                                        · linarith only [h0, h714, hlam]
                                        · linarith only [h656, h714, hlam]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        rcases p703_3 (m.d 0 1) (by simp) with h717 | h717
                                        · linarith only [h0, h717, hlam]
                                        · linarith only [h657, h717, hlam]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [h655, hlam, p703_0]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [h688, hlam, p703_0]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [hlam, p703_0]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [h657, h689, h692, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p703_1, u2ehi3]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [h692, hlam, p703_1]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [h656, hlam, p703_0]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [h689, hlam, p703_0]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [h691, hlam, p703_1]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [hlam, p703_0]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [h694, hlam, p703_1]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [h657, hlam, p703_0]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [h690, hlam, p703_0]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [h0, h657, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p703_1]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [h0, h657, h689, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p703_1, u2ehi3]
                                      · have p703_0 := h703c.1
                                        have p703_1 := h703c.2.1
                                        have p703_2 := h703c.2.2.1
                                        have p703_3 := h703c.2.2.2
                                        linarith only [hlam, p703_0]
                              · linarith only [h661, h662, h696, hc23, hc35, hlam, hphi]
                        · linarith only [h661, h662, h688, h691, hc35, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h657, h690, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h655, h688, h689, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h655, h659, h661, h688, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h740 | h740
              · rcases m.htr 0 4 5 (by decide) (by decide) with h741 | h741
                · rcases m.htr 1 2 3 (by decide) (by decide) with h742 | h742
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h743 | h743
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h744 | h744
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h745 | h745
                        · linarith only [h655, h661, h740, h745, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h747 | h747
                          · linarith only [h0, h656, h745, h747, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h661, h740, h742, h747, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h655, h742, h744, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h655, h742, h743, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h657, h742, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h661, h740, h741, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h754 | h754
                · rcases m.htr 1 2 3 (by decide) (by decide) with h755 | h755
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h756 | h756
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h757 | h757
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h758 | h758
                        · linarith only [h0, h655, h661, h758, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h760 | h760
                          · linarith only [h655, h740, h760, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h762 | h762
                            · linarith only [h0, h656, h762, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · linarith only [h0, h656, h754, h755, h758, h762, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h656, h754, h757, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h0, h655, h755, h756, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h656, h754, h755, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h768 | h768
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h769 | h769
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h770 | h770
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h771 | h771
                        · linarith only [h655, h661, h771, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h773 | h773
                          · linarith only [h655, h740, h773, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h775 | h775
                            · linarith only [h0, h656, h754, h775, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h777 | h777
                              · linarith only [h655, h661, h768, h777, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h779 | h779
                                · linarith only [h0, h657, h740, h768, h771, h775, h779, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h781 | h781
                                  · linarith only [h656, h754, h769, h781, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h783 | h783
                                    · linarith only [h656, h754, h768, h771, h783, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h655, h661, h768, h783, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h657, h770, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h655, h768, h769, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h656, h659, h768, hc23, hlam, hphi, u2ehi3]
          · linarith only [h658, h660, hc25, hlam, hphi, u2ehi2]
        · linarith only [h658, h659, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h655, h658, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h792 | h792
      · rcases m.htr 0 2 4 (by decide) (by decide) with h793 | h793
        · rcases m.htr 0 2 5 (by decide) (by decide) with h794 | h794
          · rcases m.htr 0 3 4 (by decide) (by decide) with h795 | h795
            · rcases m.htr 0 3 5 (by decide) (by decide) with h796 | h796
              · linarith only [h655, h657, h796, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h798 | h798
                · linarith only [h655, h657, h795, h798, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h800 | h800
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h801 | h801
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h802 | h802
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h803 | h803
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h804 | h804
                          · linarith only [h655, h657, h796, h802, h804, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h655, h657, h801, h803, h804, hc35, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h795, h796, h803, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h794, h802, hlam]
                    · linarith only [h0, h655, h800, h801, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h794, h800, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h811 | h811
              · linarith only [h656, h657, h795, h811, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h813 | h813
                · linarith only [h656, h657, h813, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h815 | h815
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h816 | h816
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h817 | h817
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h818 | h818
                        · linarith only [h655, h657, h795, h817, h818, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h820 | h820
                          · linarith only [h656, h657, h811, h818, h820, hlam]
                          · linarith only [h656, h657, h815, h818, h820, hc35, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h656, h794, h813, h816, h817, hc24, hc45, hlam, hphi]
                    · linarith only [h0, h655, h815, h816, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h794, h815, hc23, hlam, hphi, u2ehi4]
          · linarith only [h792, h794, hc25, hlam, hphi, u2ehi2]
        · linarith only [h792, h793, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h655, h792, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h829 | h829
    · rcases m.htr 0 2 3 (by decide) (by decide) with h830 | h830
      · rcases m.htr 0 2 4 (by decide) (by decide) with h831 | h831
        · rcases m.htr 0 2 5 (by decide) (by decide) with h832 | h832
          · rcases m.htr 0 3 4 (by decide) (by decide) with h833 | h833
            · linarith only [h655, h656, h833, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h835 | h835
              · rcases m.htr 0 4 5 (by decide) (by decide) with h836 | h836
                · rcases m.htr 1 2 3 (by decide) (by decide) with h837 | h837
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h838 | h838
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h839 | h839
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h840 | h840
                        · linarith only [h655, h833, h835, h840, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                        · linarith only [h655, h656, h837, h840, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h655, h656, h837, h838, h839, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h655, h831, h837, h838, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h829, h837, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h656, h829, h836, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h847 | h847
                · rcases m.htr 1 2 3 (by decide) (by decide) with h848 | h848
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h849 | h849
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h850 | h850
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h851 | h851
                        · linarith only [h655, h833, h847, h851, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h656, h829, h850, h851, hc34, hlam, hphi, ht23, u2ehi4]
                      · linarith only [h656, h829, h849, h850, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h655, h831, h848, h849, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h829, h830, h848, hc03, hlam, hphi, ht0b, ht5b, u5ehi1]
                · linarith only [h656, h829, h847, hlam]
          · linarith only [h831, h832, hc25, hlam, hphi, u2ehi3]
        · linarith only [h830, h831, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h655, h830, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h861 | h861
      · rcases m.htr 0 2 4 (by decide) (by decide) with h862 | h862
        · rcases m.htr 0 2 5 (by decide) (by decide) with h863 | h863
          · rcases m.htr 0 3 4 (by decide) (by decide) with h864 | h864
            · linarith only [h655, h656, h864, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h866 | h866
              · linarith only [h655, h829, h866, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h868 | h868
                · rcases m.htr 1 2 3 (by decide) (by decide) with h869 | h869
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h870 | h870
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h871 | h871
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h872 | h872
                        · linarith only [h655, h656, h864, h870, h872, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h655, h656, h869, h872, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h655, h656, h863, h869, h870, h871, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h655, h862, h869, h870, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h862, h869, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h878 | h878
                  · linarith only [h655, h656, h868, h878, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h861, h866, h878, hc01, hc35, hlam, hphi, ht12, ht23]
          · linarith only [h862, h863, hc25, hlam, hphi, u2ehi3]
        · linarith only [h861, h862, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h655, h861, hlam]

set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h655 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h884 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1bigk := hb1.1
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h885 | h885
  · rcases m.htr 0 2 3 (by decide) (by decide) with h886 | h886
    · rcases m.htr 0 2 4 (by decide) (by decide) with h887 | h887
      · rcases m.htr 0 2 5 (by decide) (by decide) with h888 | h888
        · rcases m.htr 0 3 4 (by decide) (by decide) with h889 | h889
          · rcases m.htr 0 3 5 (by decide) (by decide) with h890 | h890
            · rcases m.htr 0 4 5 (by decide) (by decide) with h891 | h891
              · rcases m.htr 1 2 3 (by decide) (by decide) with h892 | h892
                · rcases m.htr 1 2 4 (by decide) (by decide) with h893 | h893
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h894 | h894
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h895 | h895
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h896 | h896
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h897 | h897
                          · linarith only [h655, h884, h892, h897, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · linarith only [h655, h884, h891, h892, h893, h897, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h655, h885, h896, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h655, h884, h889, h895, hlam]
                    · linarith only [h655, h885, h892, h894, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h655, h885, h892, h893, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h884, h891, h892, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h905 | h905
                · rcases m.htr 1 2 4 (by decide) (by decide) with h906 | h906
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h907 | h907
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h908 | h908
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h909 | h909
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h910 | h910
                          · linarith only [h655, h884, h891, h905, h910, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h912 | h912
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h913 | h913
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h914 | h914
                                · linarith only [h884, h891, h906, h914, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h916 | h916
                                  · linarith only [h884, h891, h906, h912, h916, hlam]
                                  · rcases h1bigk with h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h0, hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h655, hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h655, h905, h906, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p918_1, u2ehi3]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h655, h905, h906, h910, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p918_1, u2ehi3]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h884, h906, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p918_1, u2ehi3]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h655, hc01, hc12, hlam, hphi, p918_1]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      rcases p918_3 (m.d 0 1) (by simp) with h927 | h927
                                      · linarith only [h0, h927, hlam]
                                      · linarith only [h884, h927, hlam]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      rcases p918_3 (m.d 0 1) (by simp) with h930 | h930
                                      · linarith only [h0, h930, hlam]
                                      · linarith only [h885, h930, hlam]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h885, h906, h910, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p918_1, u2ehi3]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h905, hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      rcases p918_3 (m.d 0 1) (by simp) with h936 | h936
                                      · linarith only [h655, h936, hlam]
                                      · linarith only [h884, h936, hlam]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      rcases p918_3 (m.d 0 1) (by simp) with h939 | h939
                                      · linarith only [h655, h939, hlam]
                                      · linarith only [h885, h939, hlam]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h884, hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h906, hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h908, hlam, p918_1]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h910, hlam, p918_1]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h885, hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h907, hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h909, hlam, p918_0]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [h885, h906, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p918_1, u2ehi3]
                                    · have p918_0 := h918c.1
                                      have p918_1 := h918c.2.1
                                      have p918_2 := h918c.2.2.1
                                      have p918_3 := h918c.2.2.2
                                      linarith only [hlam, p918_0]
                              · linarith only [h655, h885, h905, h909, h913, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h889, h891, h912, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h655, h885, h909, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h655, h885, h908, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                    · linarith only [h655, h884, h905, h906, h907, hc25, hlam, hphi, u2ehi3]
                  · linarith only [h655, h885, h905, h906, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h885, h905, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h655, h885, h890, hlam]
          · linarith only [h655, h884, h889, hlam]
        · linarith only [h886, h888, hc25, hlam, hphi, u2ehi2]
      · linarith only [h886, h887, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h963 | h963
      · linarith only [h886, h963, hc23, hlam, hphi, u2ehi3]
      · linarith only [h0, h884, h963, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h966 | h966
    · rcases m.htr 0 2 4 (by decide) (by decide) with h967 | h967
      · rcases m.htr 0 2 5 (by decide) (by decide) with h968 | h968
        · rcases m.htr 0 3 4 (by decide) (by decide) with h969 | h969
          · rcases m.htr 0 3 5 (by decide) (by decide) with h970 | h970
            · rcases m.htr 0 4 5 (by decide) (by decide) with h971 | h971
              · linarith only [h884, h885, h971, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h973 | h973
                · rcases m.htr 1 2 4 (by decide) (by decide) with h974 | h974
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h975 | h975
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h976 | h976
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h977 | h977
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h978 | h978
                          · linarith only [h884, h885, h971, h973, h977, h978, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h884, h885, h974, h978, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                        · linarith only [h0, h655, h884, h966, h970, h974, h977, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h655, h884, h974, h976, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h0, h884, h974, h975, hc25, hlam, hphi, u2ehi3]
                  · linarith only [h0, h968, h974, hc24, hlam, hphi, u2ehi4]
                · linarith only [h0, h884, h967, h973, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h986 | h986
              · linarith only [h655, h884, h970, h986, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h988 | h988
                · rcases m.htr 1 2 4 (by decide) (by decide) with h989 | h989
                  · linarith only [h655, h884, h970, h989, hc35, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h0, h968, h989, hc24, hlam, hphi, u2ehi4]
                · linarith only [h0, h884, h966, h967, h988, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
          · linarith only [h655, h884, h969, hlam]
        · linarith only [h966, h968, hc25, hlam, hphi, u2ehi2]
      · linarith only [h966, h967, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h996 | h996
      · linarith only [h966, h996, hc23, hlam, hphi, u2ehi3]
      · linarith only [h0, h884, h996, hlam]

set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h655 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h884 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h999 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1bigk := hb1.1
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1000 | h1000
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1001 | h1001
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1002 | h1002
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1003 | h1003
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1004 | h1004
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1005 | h1005
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1006 | h1006
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1007 | h1007
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1008 | h1008
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1009 | h1009
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1010 | h1010
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1011 | h1011
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1012 | h1012
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1013 | h1013
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1014 | h1014
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1015 | h1015
                                · linarith only [h1000, h1012, h1015, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases h1bigk with h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [hlam, p1017_0]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [h0, hlam, p1017_0]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [h655, hlam, p1017_0]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [h884, hlam, p1017_0]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [h1006, h1008, h1009, h884, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1017_1, u2ehi4]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [h1008, h999, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1017_1, u2ehi4]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [hlam, p1017_0]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [h655, hc01, hc12, hlam, hphi, p1017_1]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [h1008, h884, h999, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1017_1, u2ehi4]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    rcases p1017_3 (m.d 0 1) (by simp) with h1027 | h1027
                                    · linarith only [h0, h1027, hlam]
                                    · linarith only [h1027, h999, hlam]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [h1008, h999, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1017_1, u2ehi4]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [h1006, hlam, p1017_0]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [hlam, p1017_0]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [h1006, h1008, h884, h999, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1017_1, u2ehi4]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    rcases p1017_3 (m.d 0 1) (by simp) with h1034 | h1034
                                    · linarith only [h1034, h655, hlam]
                                    · linarith only [h1034, h999, hlam]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [h1008, h999, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1017_1, u2ehi4]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [h1007, hlam, p1017_0]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [h1009, hlam, p1017_1]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [hlam, p1017_0]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    rcases p1017_3 (m.d 0 1) (by simp) with h1041 | h1041
                                    · linarith only [h1041, h884, hlam]
                                    · linarith only [h1041, h999, hlam]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [h999, hlam, p1017_0]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [h1008, hlam, p1017_0]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [h1010, hlam, p1017_0]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [h1011, hlam, p1017_0]
                                  · have p1017_0 := h1017c.1
                                    have p1017_1 := h1017c.2.1
                                    have p1017_2 := h1017c.2.2.1
                                    have p1017_3 := h1017c.2.2.2
                                    linarith only [hlam, p1017_0]
                              · linarith only [h1006, h1009, h1011, h1014, h884, h999, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h1006, h1009, h1010, h1013, h884, h999, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1051 | h1051
                            · linarith only [h1003, h1006, h1012, h1051, h655, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · linarith only [h1006, h1009, h1010, h1051, h884, h999, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h1011, h884, h999, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                      · linarith only [h1008, h1009, h1010, h884, h999, hc35, hlam, hphi, ht23, u2ehi4]
                    · linarith only [h1003, h1009, h655, hlam]
                  · linarith only [h0, h1008, h999, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h1006, h1007, h655, h999, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h1006, h999, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h1005, h884, h999, hlam]
          · linarith only [h1004, h655, h999, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1062 | h1062
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1063 | h1063
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1064 | h1064
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1065 | h1065
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1066 | h1066
                  · linarith only [h1003, h1066, h655, h999, hc34, hlam, hphi, ht23, u2ehi4]
                  · linarith only [h1064, h1066, h655, h999, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h1001, h1065, hlam]
              · linarith only [h0, h1000, h1064, hlam]
            · linarith only [h1003, h1063, h655, h999, hlam]
          · linarith only [h1062, h655, h999, hlam]
      · linarith only [h1000, h1002, hc25, hlam, hphi, u2ehi2]
    · linarith only [h1000, h1001, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1075 | h1075
    · linarith only [h1000, h1075, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1077 | h1077
      · linarith only [h1000, h1077, hc23, hlam, hphi, u2ehi4]
      · linarith only [h0, h1077, h999, hlam]

end R2N4
