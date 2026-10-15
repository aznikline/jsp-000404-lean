import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3368000 in
set_option maxHeartbeats 3368000 in
theorem r1l7_22_13_15_M_IR_L_R_L_I_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3ehi := hb3.1
  have h5bigk := hb5.1
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
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
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                            · linarith only [h0, h14, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h11, h14, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                            · linarith only [h0, h17, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h11, h17, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h11, h12, h2, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                        · linarith only [h11, h21, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                            · linarith only [h0, h24, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                              · linarith only [h21, h26, h8, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
                                  · rcases h2bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi2]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      rcases p30_3 (m.d 0 2) (by simp) with h33 | h33
                                      · rcases p30_3 (m.d 1 2) (by simp) with h34 | h34
                                        · linarith only [h0, h34, hlam]
                                        · linarith only [h34, h8, hlam]
                                      · linarith only [h33, hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      rcases p30_3 (m.d 0 2) (by simp) with h38 | h38
                                      · rcases p30_3 (m.d 1 2) (by simp) with h39 | h39
                                        · linarith only [h0, h39, hlam]
                                        · linarith only [h39, h9, hlam]
                                      · linarith only [h38, hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      rcases p30_3 (m.d 0 2) (by simp) with h43 | h43
                                      · rcases p30_3 (m.d 1 2) (by simp) with h44 | h44
                                        · linarith only [h0, h44, hlam]
                                        · linarith only [h10, h44, hlam]
                                      · linarith only [h43, hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h0, hlam, p30_1]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi2]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h0, h28, hc01, hc45, hlam, hphi, ht0b, ht5b, p30_1]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi4]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h2, hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h8, hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h24, hlam, p30_1]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h26, hlam, p30_1]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h3, hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h9, hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [hc24, hlam, hphi, p30_1, u2ehi2]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h0, h26, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi2]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h4, hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h10, hlam, p30_0]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [hc25, hlam, hphi, p30_1, u2ehi2]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [h28, hlam, p30_1]
                                    · have p30_0 := h30c.1
                                      have p30_1 := h30c.2.1
                                      have p30_2 := h30c.2.2.1
                                      have p30_3 := h30c.2.2.2
                                      linarith only [hlam, p30_0]
                                  · linarith only [h0, h11, h2, h29, h5, h7, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h0, h23, h28, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                            · linarith only [h21, h70, h8, hc35, hlam, hphi, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h72 | h72
                              · linarith only [h0, h11, h2, h23, h5, h7, h72, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h74 | h74
                                · linarith only [h11, h23, h74, h8, hc24, hlam, hphi, u2ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h76 | h76
                                  · linarith only [h11, h23, h76, h8, hc34, hlam, hphi, ht23, u2ehi2]
                                  · linarith only [h0, h11, h2, h5, h7, h76, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h10, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h8, h9, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                  · linarith only [h8, h81, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h83 | h83
                    · linarith only [h0, h2, h8, h83, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h85 | h85
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h86 | h86
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h87 | h87
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h89 | h89
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h90 | h90
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h91 | h91
                                  · rcases h2bigk with h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [hlam, p92_0]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      rcases p92_3 (m.d 0 2) (by simp) with h94 | h94
                                      · rcases p92_3 (m.d 1 2) (by simp) with h95 | h95
                                        · linarith only [h0, h95, hlam]
                                        · rcases p92_3 (m.d 2 3) (by simp) with h97 | h97
                                          · linarith only [h2, h97, hlam]
                                          · linarith only [h8, h97, hlam]
                                      · linarith only [h0, h94, hlam]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [h0, h83, h88, h90, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p92_1, u2ehi1]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [h0, h83, h90, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p92_1, u2ehi1]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [h0, h83, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p92_1, u2ehi1]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [h0, hlam, p92_1]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [hlam, p92_0]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [h8, hlam, p92_0]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [h81, hlam, p92_0]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [h83, hlam, p92_0]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [h2, hlam, p92_0]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [hc23, hlam, hphi, p92_1, u2ehi1]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [hlam, p92_0]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [h0, h2, h83, h90, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p92_1, u2ehi1]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [h0, h2, h83, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p92_1, u2ehi1]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [h3, hlam, p92_0]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [hc24, hlam, hphi, p92_1, u2ehi1]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [h88, hlam, p92_0]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [hlam, p92_0]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [h0, h2, h83, h88, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p92_1, u2ehi1]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [h4, hlam, p92_0]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [hc25, hlam, hphi, p92_1, u2ehi1]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [h89, hlam, p92_0]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [h90, hlam, p92_1]
                                    · have p92_0 := h92c.1
                                      have p92_1 := h92c.2.1
                                      have p92_2 := h92c.2.2.1
                                      have p92_3 := h92c.2.2.2
                                      linarith only [hlam, p92_0]
                                  · linarith only [h0, h2, h81, h87, h88, h91, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h0, h2, h5, h7, h81, h90, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h8, h89, hc35, hlam, hphi, ht23, u2ehi1]
                            · linarith only [h8, h86, h88, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h128 | h128
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h129 | h129
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h130 | h130
                                · linarith only [h0, h128, h130, h2, h81, h87, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h0, h130, h2, h5, h7, h81, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h129, h8, h86, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · linarith only [h128, h8, h85, hlam]
                        · linarith only [h85, h86, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h136 | h136
                        · linarith only [h136, h85, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h138 | h138
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h139 | h139
                            · linarith only [h0, h139, h2, h85, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · linarith only [h0, h139, h2, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h142 | h142
                            · linarith only [h142, h8, h85, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h0, h142, h2, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h145 | h145
                · rcases m.htr 1 2 4 (by decide) (by decide) with h146 | h146
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h147 | h147
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h148 | h148
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h149 | h149
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h150 | h150
                          · linarith only [h0, h146, h150, h3, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h152 | h152
                            · linarith only [h0, h145, h152, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h152, h5, h7, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h148, h149, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h148, h5, h7, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h0, h145, h147, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h145, h146, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h159 | h159
                  · linarith only [h145, h159, hc23, hlam, hphi, u2ehi3]
                  · linarith only [h159, h3, h7, hc45, hlam, hphi, ht23, ht34, u2ehi1]
            · linarith only [h5, h6, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h163 | h163
            · linarith only [h163, h5, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h165 | h165
              · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
                · rcases m.htr 1 2 4 (by decide) (by decide) with h167 | h167
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h168 | h168
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h169 | h169
                      · linarith only [h0, h166, h169, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h171 | h171
                        · linarith only [h163, h169, h171, h2, hc34, hlam, hphi, ht23, u2ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h173 | h173
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h174 | h174
                            · linarith only [h0, h169, h174, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h176 | h176
                              · linarith only [h163, h176, h2, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h178 | h178
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h179 | h179
                                  · rcases h2bigk with h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h0, h166, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p180_1, u2ehi2]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      rcases p180_3 (m.d 0 2) (by simp) with h183 | h183
                                      · rcases p180_3 (m.d 1 2) (by simp) with h184 | h184
                                        · linarith only [h0, h184, hlam]
                                        · linarith only [h166, h184, hlam]
                                      · linarith only [h183, hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      rcases p180_3 (m.d 0 2) (by simp) with h188 | h188
                                      · rcases p180_3 (m.d 1 2) (by simp) with h189 | h189
                                        · linarith only [h0, h189, hlam]
                                        · linarith only [h167, h189, hlam]
                                      · linarith only [h188, hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      rcases p180_3 (m.d 0 2) (by simp) with h193 | h193
                                      · rcases p180_3 (m.d 1 2) (by simp) with h194 | h194
                                        · linarith only [h0, h194, hlam]
                                        · linarith only [h168, h194, hlam]
                                      · linarith only [h193, hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h0, hlam, p180_1]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p180_1, u2ehi2]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h0, h178, hc01, hc45, hlam, hphi, ht0b, ht5b, p180_1]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p180_1, u2ehi4]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h2, hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h166, hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h174, hlam, p180_1]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h176, hlam, p180_1]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h3, hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h167, hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [hc24, hlam, hphi, p180_1, u2ehi2]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h0, h167, h176, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p180_1, u2ehi2]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h4, hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h168, hlam, p180_0]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [hc25, hlam, hphi, p180_1, u2ehi2]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [h178, hlam, p180_1]
                                    · have p180_0 := h180c.1
                                      have p180_1 := h180c.2.1
                                      have p180_2 := h180c.2.2.1
                                      have p180_3 := h180c.2.2.2
                                      linarith only [hlam, p180_0]
                                  · linarith only [h179, h2, h5, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                · linarith only [h165, h178, h5, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h165, h167, h173, h5, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h0, h166, h168, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h166, h167, hc24, hlam, hphi, u2ehi2]
                · linarith only [h166, h2, h5, hc34, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h224 | h224
                · rcases m.htr 1 2 4 (by decide) (by decide) with h225 | h225
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h226 | h226
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h227 | h227
                      · linarith only [h0, h224, h227, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h229 | h229
                        · linarith only [h227, h229, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h231 | h231
                          · linarith only [h0, h165, h2, h225, h231, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h233 | h233
                            · linarith only [h2, h233, h5, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h235 | h235
                              · linarith only [h0, h2, h229, h235, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h237 | h237
                                · linarith only [h0, h165, h225, h237, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h239 | h239
                                  · linarith only [h165, h2, h239, h5, hc34, hlam, hphi, ht23, u2ehi2]
                                  · linarith only [h2, h239, h5, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h224, h226, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h224, h225, hc24, hlam, hphi, u2ehi2]
                · linarith only [h2, h224, h5, hc34, hlam, hphi, ht23, u2ehi1]
        · linarith only [h2, h4, hc25, hlam, hphi, u2ehi2]
      · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h247 | h247
      · linarith only [h2, h247, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h249 | h249
        · linarith only [h2, h249, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h251 | h251
          · rcases m.htr 0 3 5 (by decide) (by decide) with h252 | h252
            · rcases m.htr 0 4 5 (by decide) (by decide) with h253 | h253
              · rcases m.htr 1 2 3 (by decide) (by decide) with h254 | h254
                · linarith only [h0, h2, h254, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
                  · linarith only [h0, h247, h256, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h258 | h258
                    · linarith only [h0, h249, h258, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h260 | h260
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h261 | h261
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h262 | h262
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h263 | h263
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h264 | h264
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h265 | h265
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h266 | h266
                                  · rcases h2bigk with h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h249, h263, h265, hc23, hlam, hphi, p267_1, u2ehi1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h2, hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h247, hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h249, hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h0, hlam, p267_1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h254, hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h256, hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h258, hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [hc23, hlam, hphi, p267_1, u2ehi0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [hc23, hlam, hphi, p267_1, u2ehi1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [hc23, hlam, hphi, p267_1, u2ehi3]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h0, h249, hc23, hlam, hphi, p267_1, u2ehi1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h0, hc24, hlam, hphi, p267_1, u2ehi1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [hc24, hlam, hphi, p267_1, u2ehi1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h263, hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h0, h249, h263, hc23, hlam, hphi, p267_1, u2ehi1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h0, hc25, hlam, hphi, p267_1, u2ehi1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [hc25, hlam, hphi, p267_1, u2ehi1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h264, hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h265, hlam, p267_1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [hlam, p267_0]
                                  · rcases h2bigk with h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h2, hc23, hlam, hphi, p293_1, u2ehi1]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h2, hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h247, hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h249, hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h0, hlam, p293_1]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h254, hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h256, hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h258, hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [hc23, hlam, hphi, p293_1, u2ehi0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [hc23, hlam, hphi, p293_1, u2ehi1]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h247, h253, h266, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p293_1, u3ehi3]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [hc23, hlam, hphi, p293_1, u2ehi4]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h0, hc24, hlam, hphi, p293_1, u2ehi1]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [hc24, hlam, hphi, p293_1, u2ehi1]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h263, hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h263, hc23, hlam, hphi, p293_1, u2ehi4]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h0, hc25, hlam, hphi, p293_1, u2ehi1]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [hc25, hlam, hphi, p293_1, u2ehi1]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h264, hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h265, hlam, p293_1]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [hlam, p293_0]
                                · linarith only [h0, h247, h260, h262, h265, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h247, h263, h264, hc35, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h0, h2, h260, h263, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · linarith only [h2, h251, h253, h256, h262, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h2, h252, h254, h261, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h2, h251, h254, h260, hc23, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h325 | h325
                · linarith only [h0, h247, h325, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h327 | h327
                  · linarith only [h0, h247, h327, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h329 | h329
                    · linarith only [h0, h247, h253, h329, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h331 | h331
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h332 | h332
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h333 | h333
                          · linarith only [h247, h253, h325, h331, h333, hc23, hlam, hphi, u2ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h335 | h335
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h336 | h336
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h337 | h337
                                · linarith only [h0, h247, h253, h337, hc24, hlam, hphi, u2ehi1]
                                · linarith only [h0, h247, h337, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                              · linarith only [h0, h2, h252, h336, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · linarith only [h2, h251, h253, h335, hc45, hlam, hphi, ht34, u3ehi0]
                        · linarith only [h331, h332, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h251, h253, h331, hc45, hlam, hphi, ht34, u3ehi1]
            · linarith only [h251, h252, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h345 | h345
            · linarith only [h251, h345, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h347 | h347
              · rcases m.htr 1 2 3 (by decide) (by decide) with h348 | h348
                · linarith only [h0, h2, h348, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h350 | h350
                  · linarith only [h0, h2, h251, h350, hc34, hlam, hphi, ht23, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h352 | h352
                    · linarith only [h0, h249, h352, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h354 | h354
                      · linarith only [h2, h251, h348, h354, hc23, hlam, hphi, u2ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h356 | h356
                        · linarith only [h0, h2, h345, h354, h356, hc34, hlam, hphi, ht23, u2ehi1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h358 | h358
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h359 | h359
                            · linarith only [h0, h2, h251, h359, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h0, h2, h359, hc34, hlam, hphi, ht23, u2ehi1]
                          · linarith only [h251, h347, h350, h358, hc34, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h363 | h363
                · linarith only [h0, h2, h363, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h365 | h365
                  · linarith only [h0, h2, h365, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h367 | h367
                    · linarith only [h0, h249, h367, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h369 | h369
                      · linarith only [h2, h251, h363, h369, hc23, hlam, hphi, u2ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h371 | h371
                        · linarith only [h369, h371, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h373 | h373
                          · linarith only [h0, h2, h251, h347, h365, h373, hc24, hlam, hphi, u2ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h375 | h375
                            · linarith only [h0, h2, h251, h375, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h0, h2, h375, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h378 | h378
    · rcases m.htr 0 2 4 (by decide) (by decide) with h379 | h379
      · rcases m.htr 0 2 5 (by decide) (by decide) with h380 | h380
        · linarith only [h0, h1, h380, hlam]
        · linarith only [h378, h380, hc25, hlam, hphi, u2ehi2]
      · linarith only [h378, h379, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h384 | h384
      · linarith only [h378, h384, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h386 | h386
        · linarith only [h378, h386, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h388 | h388
          · rcases m.htr 0 3 5 (by decide) (by decide) with h389 | h389
            · rcases m.htr 0 4 5 (by decide) (by decide) with h390 | h390
              · rcases m.htr 1 2 3 (by decide) (by decide) with h391 | h391
                · linarith only [h0, h378, h391, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h393 | h393
                  · linarith only [h0, h1, h384, h390, h393, hc15, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h395 | h395
                    · linarith only [h0, h1, h386, h395, hlam]
                    · linarith only [h0, h1, h395, hc25, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h398 | h398
                · linarith only [h0, h1, h378, h389, h398, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h400 | h400
                  · linarith only [h0, h384, h400, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h402 | h402
                    · linarith only [h0, h1, h402, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · linarith only [h0, h1, h402, hc25, hlam, hphi, u2ehi1]
            · linarith only [h388, h389, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h406 | h406
            · linarith only [h388, h406, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h408 | h408
              · rcases m.htr 1 2 3 (by decide) (by decide) with h409 | h409
                · linarith only [h0, h378, h409, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h411 | h411
                  · linarith only [h0, h1, h384, h408, h411, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h413 | h413
                    · linarith only [h0, h1, h413, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · linarith only [h0, h1, h413, hc25, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h416 | h416
                · linarith only [h0, h378, h416, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h418 | h418
                  · linarith only [h0, h384, h418, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h420 | h420
                    · linarith only [h0, h1, h420, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · linarith only [h0, h1, h420, hc25, hlam, hphi, u2ehi1]

set_option maxHeartbeats 3368000 in
set_option maxHeartbeats 3368000 in
theorem r1l7_22_13_15_M_IR_L_R_L_I_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h423 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3ehi := hb3.1
  have h5bigk := hb5.1
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h424 | h424
  · rcases m.htr 0 2 4 (by decide) (by decide) with h425 | h425
    · rcases m.htr 0 2 5 (by decide) (by decide) with h426 | h426
      · rcases m.htr 0 3 4 (by decide) (by decide) with h427 | h427
        · rcases m.htr 0 3 5 (by decide) (by decide) with h428 | h428
          · rcases m.htr 0 4 5 (by decide) (by decide) with h429 | h429
            · rcases m.htr 1 2 3 (by decide) (by decide) with h430 | h430
              · rcases m.htr 1 2 4 (by decide) (by decide) with h431 | h431
                · rcases m.htr 1 2 5 (by decide) (by decide) with h432 | h432
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h433 | h433
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h434 | h434
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h435 | h435
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h436 | h436
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h437 | h437
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h438 | h438
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h439 | h439
                                · rcases h2bigk with h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [hlam, p440_0]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [h0, hlam, p440_0]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [h436, h439, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p440_1, u3ehi4]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    rcases p440_3 (m.d 0 2) (by simp) with h444 | h444
                                    · rcases p440_3 (m.d 1 2) (by simp) with h445 | h445
                                      · rcases p440_3 (m.d 2 3) (by simp) with h446 | h446
                                        · linarith only [h424, h446, hlam]
                                        · linarith only [h436, h446, hlam]
                                      · linarith only [h431, h445, hlam]
                                    · linarith only [h444, hlam, p440_0]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    rcases p440_3 (m.d 0 2) (by simp) with h451 | h451
                                    · rcases p440_3 (m.d 1 2) (by simp) with h452 | h452
                                      · rcases p440_3 (m.d 2 3) (by simp) with h453 | h453
                                        · linarith only [h424, h453, hlam]
                                        · linarith only [h437, h453, hlam]
                                      · linarith only [h432, h452, hlam]
                                    · linarith only [h451, hlam, p440_0]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [h0, h423, h432, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p440_1, u2ehi4]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [hlam, p440_0]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [h436, h439, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p440_1, u3ehi4]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    rcases p440_3 (m.d 0 2) (by simp) with h461 | h461
                                    · linarith only [h0, h461, hlam]
                                    · linarith only [h425, h461, hlam]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    rcases p440_3 (m.d 0 2) (by simp) with h464 | h464
                                    · linarith only [h0, h464, hlam]
                                    · linarith only [h426, h464, hlam]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [h424, hlam, p440_0]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [h430, hlam, p440_0]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [hlam, p440_0]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [h424, h436, h439, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p440_1, u3ehi4]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [h0, h424, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p440_1, u2ehi4]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [h425, hlam, p440_0]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [h431, hlam, p440_0]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [h436, hlam, p440_0]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [hlam, p440_0]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [hc24, hlam, hphi, p440_1, u2ehi4]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [h426, hlam, p440_0]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [h432, hlam, p440_0]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [h437, hlam, p440_0]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [h438, hlam, p440_1]
                                  · have p440_0 := h440c.1
                                    have p440_1 := h440c.2.1
                                    have p440_2 := h440c.2.2.1
                                    have p440_3 := h440c.2.2.2
                                    linarith only [hlam, p440_0]
                                · linarith only [h0, h423, h435, h439, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h0, h423, h435, h438, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h0, h423, h434, h437, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h485 | h485
                            · linarith only [h433, h436, h485, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                            · linarith only [h0, h423, h434, h485, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h488 | h488
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h489 | h489
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h490 | h490
                              · linarith only [h431, h435, h490, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h492 | h492
                                · linarith only [h431, h435, h488, h492, hc23, hlam, hphi, u2ehi3]
                                · rcases h2bigk with h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h0, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h0, h488, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p494_1, u3ehi3]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    rcases p494_3 (m.d 0 2) (by simp) with h498 | h498
                                    · rcases p494_3 (m.d 1 2) (by simp) with h499 | h499
                                      · rcases p494_3 (m.d 2 3) (by simp) with h500 | h500
                                        · linarith only [h424, h500, hlam]
                                        · linarith only [h488, h500, hlam]
                                      · linarith only [h431, h499, hlam]
                                    · linarith only [h498, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    rcases p494_3 (m.d 0 2) (by simp) with h505 | h505
                                    · rcases p494_3 (m.d 1 2) (by simp) with h506 | h506
                                      · rcases p494_3 (m.d 2 3) (by simp) with h507 | h507
                                        · linarith only [h424, h507, hlam]
                                        · linarith only [h489, h507, hlam]
                                      · linarith only [h432, h506, hlam]
                                    · linarith only [h505, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h0, h423, h432, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p494_1, u2ehi4]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h489, h492, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p494_1, u3ehi3]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    rcases p494_3 (m.d 0 2) (by simp) with h515 | h515
                                    · linarith only [h0, h515, hlam]
                                    · linarith only [h425, h515, hlam]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    rcases p494_3 (m.d 0 2) (by simp) with h518 | h518
                                    · linarith only [h0, h518, hlam]
                                    · linarith only [h426, h518, hlam]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h424, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h430, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hc23, hlam, hphi, p494_1, u2ehi3]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h0, h424, h489, h492, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p494_1, u3ehi3]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h425, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h431, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h488, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h490, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h426, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h432, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h489, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hc25, hlam, hphi, p494_1, u2ehi3]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hlam, p494_0]
                            · linarith only [h0, h423, h434, h489, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h429, h433, h435, h488, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h424, h428, h433, h434, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h539 | h539
                      · linarith only [h433, h539, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h541 | h541
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h542 | h542
                          · linarith only [h0, h424, h433, h542, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h544 | h544
                            · linarith only [h430, h539, h544, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h546 | h546
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h547 | h547
                                · rcases h2bigk with h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [hlam, p548_0]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [h0, hlam, p548_0]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    rcases p548_3 (m.d 0 2) (by simp) with h551 | h551
                                    · rcases p548_3 (m.d 1 2) (by simp) with h552 | h552
                                      · rcases p548_3 (m.d 2 3) (by simp) with h553 | h553
                                        · linarith only [h553, hlam, p548_0]
                                        · rcases p548_3 (m.d 2 4) (by simp) with h555 | h555
                                          · linarith only [h425, h555, hlam]
                                          · linarith only [h542, h555, hlam]
                                      · linarith only [h430, h552, hlam]
                                    · linarith only [h551, hlam, p548_0]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    rcases p548_3 (m.d 0 2) (by simp) with h560 | h560
                                    · rcases p548_3 (m.d 1 2) (by simp) with h561 | h561
                                      · rcases p548_3 (m.d 2 3) (by simp) with h562 | h562
                                        · linarith only [h424, h562, hlam]
                                        · rcases p548_3 (m.d 2 4) (by simp) with h564 | h564
                                          · linarith only [h564, hlam, p548_0]
                                          · rcases p548_3 (m.d 2 5) (by simp) with h566 | h566
                                            · linarith only [h426, h566, hlam]
                                            · rcases h5bigk with h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [hlam, p568_0]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h0, h423, h539, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p568_1, u3ehi1]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h0, h423, h544, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p568_1, u2ehi2]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h0, h423, h430, h539, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p568_1, u2ehi2]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                rcases p568_3 (m.d 0 5) (by simp) with h573 | h573
                                                · rcases p568_3 (m.d 1 5) (by simp) with h574 | h574
                                                  · linarith only [h423, h574, hlam]
                                                  · linarith only [h541, h574, hlam]
                                                · linarith only [h429, h573, hlam]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h423, hlam, p568_0]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [hlam, p568_0]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h0, h423, h544, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p568_1, u2ehi2]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h539, hlam, p568_0]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h0, h423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p568_1]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h426, hlam, p568_1]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h432, hlam, p568_1]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [hlam, p568_0]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h544, hlam, p568_1]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h546, hc02, hc45, hlam, hphi, ht0b, ht5b, p548_1, p568_1]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h428, hlam, p568_1]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h427, h432, h547, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p568_1, u2ehi4]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h0, h424, h427, h547, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p568_1, u2ehi4]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [hlam, p568_0]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                rcases p568_3 (m.d 0 5) (by simp) with h592 | h592
                                                · rcases p568_3 (m.d 1 5) (by simp) with h593 | h593
                                                  · linarith only [h539, h593, hlam]
                                                  · linarith only [h541, h593, hlam]
                                                · linarith only [h429, h592, hlam]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h429, hlam, p568_1]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h541, hlam, p568_1]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h546, hlam, p568_1]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [h547, hlam, p568_1]
                                              · have p568_0 := h568c.1
                                                have p568_1 := h568c.2.1
                                                have p568_2 := h568c.2.2.1
                                                have p568_3 := h568c.2.2.2
                                                linarith only [hlam, p568_0]
                                      · linarith only [h431, h561, hlam]
                                    · linarith only [h560, hlam, p548_0]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    rcases p548_3 (m.d 0 2) (by simp) with h604 | h604
                                    · rcases p548_3 (m.d 1 2) (by simp) with h605 | h605
                                      · rcases p548_3 (m.d 2 3) (by simp) with h606 | h606
                                        · linarith only [h424, h606, hlam]
                                        · rcases p548_3 (m.d 2 4) (by simp) with h608 | h608
                                          · linarith only [h425, h608, hlam]
                                          · linarith only [h546, h608, hlam]
                                      · linarith only [h432, h605, hlam]
                                    · linarith only [h604, hlam, p548_0]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [h424, h427, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p548_1, u3ehi3]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [hlam, p548_0]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    rcases p548_3 (m.d 0 2) (by simp) with h615 | h615
                                    · linarith only [h0, h615, hlam]
                                    · linarith only [h424, h615, hlam]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    rcases p548_3 (m.d 0 2) (by simp) with h618 | h618
                                    · linarith only [h0, h618, hlam]
                                    · linarith only [h425, h618, hlam]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    rcases p548_3 (m.d 0 2) (by simp) with h621 | h621
                                    · linarith only [h0, h621, hlam]
                                    · linarith only [h426, h621, hlam]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [h424, hlam, p548_0]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [h430, hlam, p548_0]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [hlam, p548_0]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [h542, hlam, p548_1]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [h544, hlam, p548_1]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [h425, hlam, p548_0]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [h431, hlam, p548_0]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [hc24, hlam, hphi, p548_1, u2ehi2]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [hlam, p548_0]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [h427, h431, h433, h544, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p548_1, u2ehi2]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [h426, hlam, p548_0]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [h432, hlam, p548_0]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [hc25, hlam, hphi, p548_1, u2ehi2]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [h546, hlam, p548_1]
                                  · have p548_0 := h548c.1
                                    have p548_1 := h548c.2.1
                                    have p548_2 := h548c.2.2.1
                                    have p548_3 := h548c.2.2.2
                                    linarith only [hlam, p548_0]
                                · linarith only [h0, h424, h427, h429, h430, h433, h547, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h0, h424, h427, h433, h541, h546, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h641 | h641
                          · linarith only [h430, h539, h641, hc35, hlam, hphi, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h643 | h643
                            · linarith only [h0, h424, h427, h429, h430, h433, h541, h643, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h645 | h645
                              · linarith only [h430, h433, h541, h645, hc24, hlam, hphi, u2ehi2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h647 | h647
                                · linarith only [h430, h433, h541, h647, hc34, hlam, hphi, ht23, u2ehi2]
                                · linarith only [h0, h424, h427, h429, h430, h433, h647, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h424, h432, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h423, h426, h431, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h423, h426, h430, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h653 | h653
              · rcases m.htr 1 2 4 (by decide) (by decide) with h654 | h654
                · rcases m.htr 1 2 5 (by decide) (by decide) with h655 | h655
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h656 | h656
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h657 | h657
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h658 | h658
                        · linarith only [h0, h423, h425, h429, h658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h660 | h660
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h661 | h661
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h662 | h662
                              · linarith only [h425, h429, h662, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h664 | h664
                                · linarith only [h425, h429, h664, hc34, hlam, hphi, ht23, u2ehi3]
                                · rcases h2bigk with h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [hlam, p666_0]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [h0, hlam, p666_0]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [h0, h660, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p666_1, u3ehi3]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    rcases p666_3 (m.d 0 2) (by simp) with h670 | h670
                                    · rcases p666_3 (m.d 1 2) (by simp) with h671 | h671
                                      · rcases p666_3 (m.d 2 3) (by simp) with h672 | h672
                                        · linarith only [h424, h672, hlam]
                                        · linarith only [h660, h672, hlam]
                                      · linarith only [h654, h671, hlam]
                                    · linarith only [h670, hlam, p666_0]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    rcases p666_3 (m.d 0 2) (by simp) with h677 | h677
                                    · rcases p666_3 (m.d 1 2) (by simp) with h678 | h678
                                      · rcases p666_3 (m.d 2 3) (by simp) with h679 | h679
                                        · linarith only [h424, h679, hlam]
                                        · linarith only [h661, h679, hlam]
                                      · linarith only [h655, h678, hlam]
                                    · linarith only [h677, hlam, p666_0]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [h0, h423, h654, h658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p666_1, u2ehi3]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [hlam, p666_0]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [h661, h664, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p666_1, u3ehi3]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    rcases p666_3 (m.d 0 2) (by simp) with h687 | h687
                                    · linarith only [h0, h687, hlam]
                                    · linarith only [h425, h687, hlam]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    rcases p666_3 (m.d 0 2) (by simp) with h690 | h690
                                    · linarith only [h0, h690, hlam]
                                    · linarith only [h426, h690, hlam]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [h424, hlam, p666_0]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [h653, hlam, p666_0]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [hlam, p666_0]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [h424, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p666_1, u2ehi3]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [h0, h424, h662, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p666_1, u2ehi3]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [h425, hlam, p666_0]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [h654, hlam, p666_0]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [h660, hlam, p666_0]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [hlam, p666_0]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [h662, hlam, p666_0]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [h426, hlam, p666_0]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [h655, hlam, p666_0]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [h661, hlam, p666_0]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [hc25, hlam, hphi, p666_1, u2ehi3]
                                  · have p666_0 := h666c.1
                                    have p666_1 := h666c.2.1
                                    have p666_2 := h666c.2.2.1
                                    have p666_3 := h666c.2.2.2
                                    linarith only [hlam, p666_0]
                            · linarith only [h0, h423, h657, h661, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h427, h429, h660, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h656, h657, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h427, h429, h656, hc45, hlam, hphi, ht34, u3ehi1]
                  · linarith only [h0, h424, h655, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h423, h426, h654, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h423, h425, h429, h653, hc23, hlam, hphi, u2ehi3]
          · linarith only [h427, h428, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h716 | h716
          · linarith only [h427, h716, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h718 | h718
            · rcases m.htr 1 2 3 (by decide) (by decide) with h719 | h719
              · rcases m.htr 1 2 4 (by decide) (by decide) with h720 | h720
                · rcases m.htr 1 2 5 (by decide) (by decide) with h721 | h721
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h722 | h722
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h723 | h723
                      · linarith only [h0, h423, h424, h716, h723, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h722, h723, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h726 | h726
                      · linarith only [h722, h726, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h728 | h728
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h729 | h729
                          · linarith only [h0, h423, h719, h726, h729, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h731 | h731
                            · linarith only [h424, h716, h731, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h733 | h733
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h734 | h734
                                · rcases h2bigk with h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [hlam, p735_0]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [h0, hlam, p735_0]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    rcases p735_3 (m.d 0 2) (by simp) with h738 | h738
                                    · rcases p735_3 (m.d 1 2) (by simp) with h739 | h739
                                      · rcases p735_3 (m.d 2 3) (by simp) with h740 | h740
                                        · linarith only [h740, hlam, p735_0]
                                        · rcases p735_3 (m.d 2 4) (by simp) with h742 | h742
                                          · linarith only [h425, h742, hlam]
                                          · linarith only [h729, h742, hlam]
                                      · linarith only [h719, h739, hlam]
                                    · linarith only [h738, hlam, p735_0]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    rcases p735_3 (m.d 0 2) (by simp) with h747 | h747
                                    · rcases p735_3 (m.d 1 2) (by simp) with h748 | h748
                                      · rcases p735_3 (m.d 2 3) (by simp) with h749 | h749
                                        · linarith only [h424, h749, hlam]
                                        · rcases p735_3 (m.d 2 4) (by simp) with h751 | h751
                                          · linarith only [h751, hlam, p735_0]
                                          · rcases p735_3 (m.d 2 5) (by simp) with h753 | h753
                                            · linarith only [h426, h753, hlam]
                                            · rcases h5bigk with h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [hlam, p755_0]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [h0, h423, h719, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi2]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [h0, h423, h731, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi2]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [h716, hlam, p755_0]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                rcases p755_3 (m.d 0 5) (by simp) with h760 | h760
                                                · rcases p755_3 (m.d 1 5) (by simp) with h761 | h761
                                                  · linarith only [h423, h761, hlam]
                                                  · linarith only [h728, h761, hlam]
                                                · linarith only [h718, h760, hlam]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [h423, hlam, p755_0]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [hlam, p755_0]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [h0, h423, h731, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi2]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [h726, hlam, p755_0]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [h0, h423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p755_1]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [h426, hlam, p755_1]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [h721, hlam, p755_1]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [hlam, p755_0]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [h731, hlam, p755_1]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [h733, hc02, hc45, hlam, hphi, ht0b, ht5b, p735_1, p755_1]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [h426, hc35, hlam, hphi, ht23, p755_1, u2ehi4]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [h721, hc35, hlam, hphi, ht23, p755_1, u2ehi4]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [hc35, hlam, hphi, ht23, p755_1, u2ehi4]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [hlam, p755_0]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                rcases p755_3 (m.d 0 5) (by simp) with h779 | h779
                                                · linarith only [h716, h779, hlam]
                                                · linarith only [h718, h779, hlam]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [h718, hlam, p755_1]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [h728, hlam, p755_1]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [h733, hlam, p755_1]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [h734, hlam, p755_1]
                                              · have p755_0 := h755c.1
                                                have p755_1 := h755c.2.1
                                                have p755_2 := h755c.2.2.1
                                                have p755_3 := h755c.2.2.2
                                                linarith only [hlam, p755_0]
                                      · linarith only [h720, h748, hlam]
                                    · linarith only [h747, hlam, p735_0]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    rcases p735_3 (m.d 0 2) (by simp) with h789 | h789
                                    · rcases p735_3 (m.d 1 2) (by simp) with h790 | h790
                                      · rcases p735_3 (m.d 2 3) (by simp) with h791 | h791
                                        · linarith only [h424, h791, hlam]
                                        · rcases p735_3 (m.d 2 4) (by simp) with h793 | h793
                                          · linarith only [h425, h793, hlam]
                                          · linarith only [h733, h793, hlam]
                                      · linarith only [h721, h790, hlam]
                                    · linarith only [h789, hlam, p735_0]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [h0, h423, h719, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p735_1, u2ehi2]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [hlam, p735_0]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    rcases p735_3 (m.d 0 2) (by simp) with h800 | h800
                                    · linarith only [h0, h800, hlam]
                                    · linarith only [h424, h800, hlam]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    rcases p735_3 (m.d 0 2) (by simp) with h803 | h803
                                    · linarith only [h0, h803, hlam]
                                    · linarith only [h425, h803, hlam]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    rcases p735_3 (m.d 0 2) (by simp) with h806 | h806
                                    · linarith only [h0, h806, hlam]
                                    · linarith only [h426, h806, hlam]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [h424, hlam, p735_0]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [h719, hlam, p735_0]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [hlam, p735_0]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [h729, hlam, p735_1]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [h731, hlam, p735_1]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [h425, hlam, p735_0]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [h720, hlam, p735_0]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [hc24, hlam, hphi, p735_1, u2ehi2]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [hlam, p735_0]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [h0, h425, h731, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p735_1, u2ehi2]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [h426, hlam, p735_0]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [h721, hlam, p735_0]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [hc25, hlam, hphi, p735_1, u2ehi2]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [h733, hlam, p735_1]
                                  · have p735_0 := h735c.1
                                    have p735_1 := h735c.2.1
                                    have p735_2 := h735c.2.2.1
                                    have p735_3 := h735c.2.2.2
                                    linarith only [hlam, p735_0]
                                · linarith only [h424, h427, h734, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · linarith only [h0, h423, h728, h733, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h427, h718, h722, h728, hc34, hlam, hphi, u3ehi1]
                  · linarith only [h0, h424, h721, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h423, h426, h720, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h423, h424, h716, h719, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h830 | h830
              · rcases m.htr 1 2 4 (by decide) (by decide) with h831 | h831
                · rcases m.htr 1 2 5 (by decide) (by decide) with h832 | h832
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h833 | h833
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h834 | h834
                      · linarith only [h0, h423, h424, h716, h834, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h833, h834, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h837 | h837
                      · linarith only [h833, h837, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h839 | h839
                        · linarith only [h425, h718, h833, h839, hc34, hlam, hphi, ht23, u2ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h841 | h841
                          · linarith only [h0, h423, h830, h833, h839, h841, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h843 | h843
                            · linarith only [h0, h423, h830, h833, h839, h843, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h845 | h845
                              · linarith only [h424, h427, h718, h845, hc24, hlam, hphi, u2ehi2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h847 | h847
                                · linarith only [h424, h427, h718, h847, hc34, hlam, hphi, ht23, u2ehi2]
                                · linarith only [h424, h427, h847, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h424, h832, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h423, h424, h425, h427, h718, h831, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h0, h424, h427, h830, hc34, hlam, hphi, ht23, u2ehi0]
      · linarith only [h424, h426, hc25, hlam, hphi, u2ehi2]
    · linarith only [h424, h425, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h855 | h855
    · linarith only [h424, h855, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h857 | h857
      · linarith only [h424, h857, hc23, hlam, hphi, u2ehi4]
      · linarith only [h0, h423, h857, hlam]

end R2N4
