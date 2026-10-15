import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_R_L_I_L_R_M_IR_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
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
                                · linarith only [h0, h10, h16, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                                  · linarith only [h0, h10, h13, h16, h18, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
                                    · linarith only [h0, h10, h13, h16, h20, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · linarith only [h0, h10, h13, h15, h20, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                                · linarith only [h0, h10, h23, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                                  · linarith only [h0, h13, h15, h23, h25, h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h27 | h27
                                    · linarith only [h15, h27, hc24, hlam, hphi, ht12, u1ehi3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
                                      · linarith only [h13, h15, h29, hlam]
                                      · rcases h2bigk with h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h0, h11, hc01, hlam, hphi, ht0b, ht45, ht5b, p31_1, u4ehi2]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h13, h15, h23, h4, h7, h9, hlam, p31_2]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          rcases p31_3 (m.d 0 2) (by simp) with h35 | h35
                                          · rcases p31_3 (m.d 1 2) (by simp) with h36 | h36
                                            · linarith only [h0, h36, hlam]
                                            · linarith only [h11, h36, hlam]
                                          · linarith only [h35, hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          rcases p31_3 (m.d 0 2) (by simp) with h40 | h40
                                          · rcases p31_3 (m.d 1 2) (by simp) with h41 | h41
                                            · linarith only [h0, h41, hlam]
                                            · linarith only [h12, h41, hlam]
                                          · linarith only [h40, hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h0, hlam, p31_1]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          rcases p31_3 (m.d 0 2) (by simp) with h47 | h47
                                          · rcases p31_3 (m.d 1 2) (by simp) with h48 | h48
                                            · rcases p31_3 (m.d 2 3) (by simp) with h49 | h49
                                              · linarith only [h49, hlam, p31_0]
                                              · rcases p31_3 (m.d 2 4) (by simp) with h51 | h51
                                                · linarith only [h11, h51, hlam]
                                                · linarith only [h23, h51, hlam]
                                            · linarith only [h48, hlam, p31_0]
                                          · linarith only [h4, h47, hlam]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p31_1, u4ehi2]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p31_1, u5ehi2]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h4, hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h10, hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h23, hlam, p31_1]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h25, hlam, p31_1]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h5, hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h11, hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p31_1]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h27, hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h6, hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h12, hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p31_1]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h0, h14, h15, h25, h4, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht45, ht5b, p31_1, u1ehi3, u4ehi2]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [hlam, p31_0]
                            · linarith only [h0, h13, h14, h4, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                            · linarith only [h0, h13, h4, h7, h74, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                                · linarith only [h13, h77, hc23, hlam, hphi, ht12, u1ehi2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h79 | h79
                                  · linarith only [h0, h10, h79, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h81 | h81
                                    · linarith only [h0, h11, h81, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                    · linarith only [h0, h13, h4, h7, h76, h81, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                                · linarith only [h0, h10, h13, h4, h7, h76, h84, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h86 | h86
                                  · linarith only [h0, h10, h13, h4, h7, h74, h76, h86, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h88 | h88
                                    · linarith only [h13, h76, h88, hc24, hlam, hphi, ht12, u1ehi2]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h90 | h90
                                      · linarith only [h13, h76, h90, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                      · linarith only [h0, h13, h4, h7, h9, h90, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                        · linarith only [h0, h11, h12, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h94 | h94
                        · linarith only [h0, h11, h5, h94, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
                          · linarith only [h0, h10, h11, h5, h96, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h98 | h98
                            · linarith only [h0, h10, h11, h5, h98, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h100 | h100
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h101 | h101
                                · linarith only [h0, h10, h101, h11, h5, h96, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h103 | h103
                                  · linarith only [h0, h10, h101, h103, h11, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h105 | h105
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h106 | h106
                                      · rcases h2bigk with h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          rcases p107_3 (m.d 0 2) (by simp) with h109 | h109
                                          · rcases p107_3 (m.d 1 2) (by simp) with h110 | h110
                                            · linarith only [h0, h110, hlam]
                                            · rcases p107_3 (m.d 2 3) (by simp) with h112 | h112
                                              · linarith only [h112, h4, hlam]
                                              · rcases p107_3 (m.d 2 4) (by simp) with h114 | h114
                                                · linarith only [h114, h5, hlam]
                                                · linarith only [h11, h114, hlam]
                                          · linarith only [h0, h109, hlam]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h10, h101, h105, h4, h7, h94, hlam, p107_2]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h0, h10, h105, h94, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p107_1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h0, h94, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p107_1, u1ehi1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h0, hlam, p107_1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h103, h94, hc23, hc35, hlam, hphi, p107_1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h11, hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h94, hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h4, hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h10, hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h101, hlam, p107_1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h103, hlam, p107_1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h5, hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p107_1, u1ehi1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          rcases p107_3 (m.d 0 2) (by simp) with h133 | h133
                                          · rcases p107_3 (m.d 1 2) (by simp) with h134 | h134
                                            · linarith only [h11, h134, hlam]
                                            · linarith only [h10, h134, hlam]
                                          · linarith only [h133, h4, hlam]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h0, h101, h4, h7, hc01, hlam, hphi, ht0b, ht5b, p107_1, u5ehi2]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h6, hlam, p107_0]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h10, hc25, hlam, hphi, ht12, p107_1, u1ehi2]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          rcases p107_3 (m.d 0 2) (by simp) with h142 | h142
                                          · rcases p107_3 (m.d 1 2) (by simp) with h143 | h143
                                            · linarith only [h143, h94, hlam]
                                            · linarith only [h10, h143, hlam]
                                          · linarith only [h142, h4, hlam]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [h105, hlam, p107_1]
                                        · have p107_0 := h107c.1
                                          have p107_1 := h107c.2.1
                                          have p107_2 := h107c.2.2.1
                                          have p107_3 := h107c.2.2.2
                                          linarith only [hlam, p107_0]
                                      · linarith only [h100, h101, h106, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                    · linarith only [h100, h105, h11, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h151 | h151
                                · linarith only [h10, h11, h151, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h153 | h153
                                  · linarith only [h0, h10, h100, h11, h153, h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h155 | h155
                                    · linarith only [h10, h100, h11, h155, hc24, hlam, hphi, ht12, u1ehi2]
                                    · linarith only [h0, h10, h11, h155, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h158 | h158
                      · linarith only [h0, h10, h158, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h160 | h160
                        · linarith only [h0, h10, h160, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h162 | h162
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h163 | h163
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h164 | h164
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h166 | h166
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h167 | h167
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h168 | h168
                                      · linarith only [h1, h162, h168, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                      · linarith only [h164, h168, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                    · linarith only [h158, h164, h167, hlam]
                                  · linarith only [h10, h163, h166, hlam]
                                · linarith only [h0, h10, h163, h165, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h174 | h174
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h175 | h175
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h176 | h176
                                    · linarith only [h158, h164, h174, h176, hc23, hlam, hphi, ht12, u1ehi1]
                                    · linarith only [h158, h176, h7, h9, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                                  · linarith only [h10, h163, h175, hlam]
                                · linarith only [h10, h162, h163, h174, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h162, h163, h4, h8, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h182 | h182
                            · linarith only [h0, h162, h182, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h184 | h184
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h185 | h185
                                · linarith only [h162, h185, hc23, hlam, hphi, ht12, u1ehi2]
                                · linarith only [h0, h10, h185, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h188 | h188
                                · linarith only [h0, h162, h188, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                                · linarith only [h10, h188, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h191 | h191
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h192 | h192
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h193 | h193
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h194 | h194
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h195 | h195
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h196 | h196
                              · linarith only [h196, h2, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                                · linarith only [h0, h191, h198, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h200 | h200
                                  · linarith only [h194, h198, h200, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h202 | h202
                                    · linarith only [h202, h5, h9, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h204 | h204
                                      · linarith only [h194, h2, h204, h9, hlam]
                                      · rcases h2bigk with h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [hlam, p206_0]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [h191, h195, h200, h202, hc02, hlam, hphi, ht0b, ht45, ht5b, p206_1, u4ehi2]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          rcases p206_3 (m.d 0 2) (by simp) with h209 | h209
                                          · rcases p206_3 (m.d 1 2) (by simp) with h210 | h210
                                            · linarith only [h0, h210, hlam]
                                            · linarith only [h191, h210, hlam]
                                          · linarith only [h209, hlam, p206_0]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          rcases p206_3 (m.d 0 2) (by simp) with h214 | h214
                                          · rcases p206_3 (m.d 1 2) (by simp) with h215 | h215
                                            · linarith only [h0, h215, hlam]
                                            · linarith only [h192, h215, hlam]
                                          · linarith only [h214, hlam, p206_0]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          rcases p206_3 (m.d 0 2) (by simp) with h219 | h219
                                          · rcases p206_3 (m.d 1 2) (by simp) with h220 | h220
                                            · linarith only [h0, h220, hlam]
                                            · linarith only [h193, h220, hlam]
                                          · linarith only [h219, hlam, p206_0]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [h0, hlam, p206_1]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [hlam, p206_0]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          rcases p206_3 (m.d 0 2) (by simp) with h226 | h226
                                          · rcases p206_3 (m.d 1 2) (by simp) with h227 | h227
                                            · rcases p206_3 (m.d 2 3) (by simp) with h228 | h228
                                              · linarith only [h228, hlam, p206_0]
                                              · rcases p206_3 (m.d 2 4) (by simp) with h230 | h230
                                                · linarith only [h192, h230, hlam]
                                                · linarith only [h198, h230, hlam]
                                            · linarith only [h227, hlam, p206_0]
                                          · linarith only [h226, h4, hlam]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p206_1, u4ehi2]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [h0, h202, hc01, hlam, hphi, ht0b, ht45, ht5b, p206_1, u4ehi2]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [h4, hlam, p206_0]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [h191, hlam, p206_0]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [hlam, p206_0]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [h198, hlam, p206_1]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [h200, hlam, p206_1]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [h5, hlam, p206_0]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [h192, hlam, p206_0]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [h1, h195, h200, h202, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p206_1]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [hlam, p206_0]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [h202, hlam, p206_0]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [h6, hlam, p206_0]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [h193, hlam, p206_0]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [h0, h193, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p206_1]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [h0, h191, h195, h200, hc01, hlam, hphi, ht0b, ht45, ht5b, p206_1, u4ehi2]
                                        · have p206_0 := h206c.1
                                          have p206_1 := h206c.2.1
                                          have p206_2 := h206c.2.2.1
                                          have p206_3 := h206c.2.2.2
                                          linarith only [hlam, p206_0]
                            · linarith only [h0, h194, h195, h4, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h194, h7, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                        · linarith only [h0, h192, h193, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h192, h5, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
                      · linarith only [h0, h191, h256, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h256, h5, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h259 | h259
                  · linarith only [h259, h7, h8, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h261 | h261
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h262 | h262
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h263 | h263
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h265 | h265
                            · linarith only [h1, h265, h8, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h267 | h267
                              · linarith only [h2, h259, h267, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h269 | h269
                                · linarith only [h0, h261, h269, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · linarith only [h1, h264, h269, h8, hc23, hc35, hlam, hphi]
                          · linarith only [h264, h7, h8, hc13, hc35, hlam, hphi]
                        · linarith only [h0, h262, h263, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h262, h5, h7, h8, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h261, h4, h8, hc35, hlam, hphi, ht12, ht23, u1ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h276 | h276
                · rcases m.htr 0 4 5 (by decide) (by decide) with h277 | h277
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h278 | h278
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h279 | h279
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h280 | h280
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h281 | h281
                          · linarith only [h276, h281, h7, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h283 | h283
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h284 | h284
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h285 | h285
                                · linarith only [h1, h278, h283, h285, h7, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h287 | h287
                                  · linarith only [h0, h278, h287, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                  · linarith only [h1, h283, h287, h7, hc23, hc34, hlam, hphi]
                              · linarith only [h277, h281, h283, h284, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h276, h283, h7, hc13, hc34, hlam, hphi]
                        · linarith only [h279, h280, h6, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h293 | h293
                        · linarith only [h0, h279, h293, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                        · linarith only [h276, h278, h293, h6, h7, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                    · linarith only [h278, h4, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h276, h277, h7, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h298 | h298
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h299 | h299
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h300 | h300
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h301 | h301
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h302 | h302
                          · linarith only [h1, h302, h7, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h304 | h304
                            · linarith only [h1, h276, h304, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h306 | h306
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h307 | h307
                                · linarith only [h1, h299, h307, h7, hc12, hlam, hphi, u1ehi2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h309 | h309
                                  · linarith only [h1, h276, h299, h309, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h311 | h311
                                    · linarith only [h0, h300, h311, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                    · linarith only [h2, h306, h311, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                              · linarith only [h298, h306, h7, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                        · linarith only [h0, h300, h301, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h316 | h316
                        · linarith only [h300, h316, h5, hc02, hlam, hphi, ht0b, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h318 | h318
                          · linarith only [h1, h298, h318, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h320 | h320
                            · linarith only [h0, h276, h299, h300, h320, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h322 | h322
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h323 | h323
                                · linarith only [h298, h299, h316, h323, h6, h7, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h325 | h325
                                  · linarith only [h276, h299, h316, h325, h6, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h327 | h327
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h328 | h328
                                      · rcases h2bigk with h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [hlam, p329_0]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          rcases p329_3 (m.d 0 2) (by simp) with h331 | h331
                                          · rcases p329_3 (m.d 1 2) (by simp) with h332 | h332
                                            · linarith only [h0, h332, hlam]
                                            · rcases p329_3 (m.d 2 3) (by simp) with h334 | h334
                                              · linarith only [h334, h4, hlam]
                                              · rcases p329_3 (m.d 2 4) (by simp) with h336 | h336
                                                · linarith only [h336, h5, hlam]
                                                · linarith only [h300, h336, hlam]
                                          · linarith only [h0, h331, hlam]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [h299, h316, h327, h5, hlam, p329_2]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [h0, h299, h316, h327, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p329_1, u1ehi2]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [h0, h299, h316, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p329_1, u1ehi2]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [h0, hlam, p329_1]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [hlam, p329_0]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [h298, h316, h6, h7, hc23, hc34, hlam, hphi, p329_1]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [h300, hlam, p329_0]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [h316, hlam, p329_0]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [h4, hlam, p329_0]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [h299, hlam, p329_0]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [hlam, p329_0]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [h323, hlam, p329_1]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [h325, hlam, p329_1]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [h5, hlam, p329_0]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [h0, h299, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p329_1, u1ehi2]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          rcases p329_3 (m.d 0 2) (by simp) with h355 | h355
                                          · rcases p329_3 (m.d 1 2) (by simp) with h356 | h356
                                            · linarith only [h300, h356, hlam]
                                            · linarith only [h299, h356, hlam]
                                          · linarith only [h355, h4, hlam]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [hlam, p329_0]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht5b, p329_1, u5ehi2]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [h6, hlam, p329_0]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [h299, hc25, hlam, hphi, ht12, p329_1, u1ehi2]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          rcases p329_3 (m.d 0 2) (by simp) with h364 | h364
                                          · rcases p329_3 (m.d 1 2) (by simp) with h365 | h365
                                            · linarith only [h316, h365, hlam]
                                            · linarith only [h299, h365, hlam]
                                          · linarith only [h364, h4, hlam]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [h327, hlam, p329_1]
                                        · have p329_0 := h329c.1
                                          have p329_1 := h329c.2.1
                                          have p329_2 := h329c.2.2.1
                                          have p329_3 := h329c.2.2.2
                                          linarith only [hlam, p329_0]
                                      · linarith only [h2, h322, h328, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                                    · linarith only [h300, h322, h327, hlam]
                              · linarith only [h298, h322, h7, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · linarith only [h299, h4, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h375 | h375
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h376 | h376
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h377 | h377
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h378 | h378
                          · linarith only [h1, h298, h378, h7, hc45, hlam, hphi, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h380 | h380
                            · linarith only [h1, h276, h380, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h382 | h382
                              · linarith only [h2, h298, h382, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h384 | h384
                                · linarith only [h1, h375, h384, h7, hc12, hlam, hphi, u1ehi2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h386 | h386
                                  · linarith only [h1, h276, h375, h386, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h388 | h388
                                    · linarith only [h2, h298, h378, h388, hc24, hlam, hphi, ht12, u1ehi2]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h390 | h390
                                      · linarith only [h2, h298, h378, h390, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                      · linarith only [h1, h390, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                        · linarith only [h0, h376, h377, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h298, h375, h376, h5, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h375, h4, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h396 | h396
              · rcases m.htr 0 3 5 (by decide) (by decide) with h397 | h397
                · linarith only [h397, h4, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h399 | h399
                  · linarith only [h399, h5, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h401 | h401
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h402 | h402
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h403 | h403
                        · linarith only [h0, h403, h6, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h405 | h405
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h406 | h406
                            · linarith only [h1, h397, h406, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h408 | h408
                              · linarith only [h2, h399, h408, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h410 | h410
                                · linarith only [h0, h401, h410, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                · linarith only [h396, h397, h410, hc23, hc35, hlam, hphi]
                          · linarith only [h396, h397, h405, hc13, hc35, hlam, hphi]
                      · linarith only [h402, h5, h6, hc12, hc25, hlam, hphi]
                    · linarith only [h4, h401, h6, hc25, hlam, hphi, ht12, u1ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h416 | h416
                · linarith only [h396, h416, h5, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h418 | h418
                  · linarith only [h418, h5, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h420 | h420
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h421 | h421
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h422 | h422
                        · linarith only [h0, h422, h6, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h424 | h424
                          · linarith only [h1, h396, h424, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h426 | h426
                            · linarith only [h1, h416, h426, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h428 | h428
                              · linarith only [h2, h418, h428, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h430 | h430
                                · linarith only [h0, h1, h396, h420, h430, h6, hc25, hlam, hphi, ht12, u1ehi2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h432 | h432
                                  · linarith only [h0, h1, h416, h421, h430, h432, h6, hc25, hlam, hphi, ht12, u1ehi2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h434 | h434
                                    · linarith only [h0, h1, h396, h418, h421, h432, h434, h6, hc35, hlam, hphi, ht12, ht23, u1ehi2]
                                    · linarith only [h0, h421, h434, h6, hc45, hlam, hphi, u4ehi2]
                      · linarith only [h421, h5, h6, hc12, hc25, hlam, hphi]
                    · linarith only [h4, h420, h6, hc25, hlam, hphi, ht12, u1ehi1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h439 | h439
            · rcases m.htr 0 3 4 (by decide) (by decide) with h440 | h440
              · linarith only [h4, h440, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h442 | h442
                · rcases m.htr 0 4 5 (by decide) (by decide) with h443 | h443
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h444 | h444
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h445 | h445
                      · linarith only [h439, h445, h5, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h447 | h447
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h448 | h448
                          · linarith only [h440, h442, h448, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h450 | h450
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h451 | h451
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h452 | h452
                                · linarith only [h0, h1, h440, h444, h450, h452, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h454 | h454
                                  · linarith only [h0, h444, h452, h454, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                                  · linarith only [h1, h4, h450, h452, h454, h5, hc23, hc34, hlam, hphi]
                              · linarith only [h440, h443, h451, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                            · linarith only [h4, h442, h450, h5, hc24, hlam, hphi, ht12, u1ehi2]
                        · linarith only [h439, h447, h5, hc12, hc24, hlam, hphi]
                    · linarith only [h4, h444, h5, hc24, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h4, h442, h443, h5, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h462 | h462
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h463 | h463
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h464 | h464
                      · linarith only [h439, h464, h5, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h466 | h466
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h467 | h467
                          · linarith only [h1, h440, h467, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h469 | h469
                            · linarith only [h1, h442, h469, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h471 | h471
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h472 | h472
                                · linarith only [h0, h1, h440, h463, h472, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h474 | h474
                                  · linarith only [h0, h1, h442, h463, h472, h474, h5, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h476 | h476
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h477 | h477
                                      · rcases h2bigk with h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c | h478c
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [hlam, p478_0]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h472, h5, hc12, hc34, hlam, hphi, ht23, p478_1]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h472, h5, hc23, hc34, hlam, hphi, p478_1]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h5, hlam, p478_0]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h472, h476, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p478_1, u4ehi4]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h0, hlam, p478_1]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [hlam, p478_0]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h0, h472, h5, hc23, hc34, hlam, hphi, p478_1]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h464, hlam, p478_0]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h0, h476, hc01, hlam, hphi, ht0b, ht45, ht5b, p478_1, u4ehi4]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h4, hlam, p478_0]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h463, hlam, p478_0]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [hlam, p478_0]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h472, hlam, p478_1]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h474, hlam, p478_1]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h3, h439, h472, hc34, hlam, hphi, ht12, ht23, p478_1, u1ehi4]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h472, hc34, hlam, hphi, ht12, ht23, p478_1, u1ehi1]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          rcases p478_3 (m.d 0 2) (by simp) with h496 | h496
                                          · linarith only [h496, h5, hlam]
                                          · linarith only [h4, h496, hlam]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [hlam, p478_0]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          rcases p478_3 (m.d 0 2) (by simp) with h500 | h500
                                          · linarith only [h5, h500, hlam]
                                          · linarith only [h439, h500, hlam]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h439, hlam, p478_0]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h466, hlam, p478_0]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h0, h466, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p478_1]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [h476, hlam, p478_1]
                                        · have p478_0 := h478c.1
                                          have p478_1 := h478c.2.1
                                          have p478_2 := h478c.2.2.1
                                          have p478_3 := h478c.2.2.2
                                          linarith only [hlam, p478_0]
                                      · linarith only [h0, h466, h472, h476, h477, h5, hlam]
                                    · linarith only [h0, h466, h476, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                              · linarith only [h440, h462, h471, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                        · linarith only [h439, h466, h5, hc24, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h4, h463, h5, hc24, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h439, h462, h5, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h514 | h514
              · linarith only [h4, h5, h514, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h516 | h516
                · linarith only [h4, h439, h516, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h518 | h518
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h519 | h519
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h520 | h520
                      · linarith only [h0, h5, h520, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h522 | h522
                        · linarith only [h1, h4, h439, h522, hc12, hlam, hphi, u1ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h524 | h524
                          · linarith only [h1, h514, h524, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h526 | h526
                            · linarith only [h1, h516, h526, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h528 | h528
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h529 | h529
                                · linarith only [h0, h1, h514, h519, h529, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h531 | h531
                                  · linarith only [h0, h5, h519, h529, h531, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h533 | h533
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h534 | h534
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
                                          linarith only [h439, h529, h533, hc12, hc34, hlam, hphi, ht23, p535_1]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [h439, h529, h533, hc23, hc34, hlam, hphi, p535_1]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [h5, hlam, p535_0]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [h439, hlam, p535_0]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [h0, hlam, p535_1]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [hlam, p535_0]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [h0, h439, h529, h533, hc23, hc34, hlam, hphi, p535_1]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [h520, hlam, p535_0]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [h522, hlam, p535_0]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [h4, hlam, p535_0]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [h519, hlam, p535_0]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [hlam, p535_0]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [h529, hlam, p535_1]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [h531, hlam, p535_1]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [h0, h529, hc34, hlam, hphi, ht12, ht23, p535_1, u1ehi1]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [h519, h529, hc34, hlam, hphi, ht12, ht23, p535_1, u1ehi2]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          rcases p535_3 (m.d 0 2) (by simp) with h553 | h553
                                          · linarith only [h5, h553, hlam]
                                          · linarith only [h4, h553, hlam]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [hlam, p535_0]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [h1, h4, h439, h529, hc34, hlam, hphi, ht12, ht23, p535_1, u1ehi2]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [h1, h4, hc25, hlam, hphi, ht12, p535_1, u1ehi2]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [h519, hc25, hlam, hphi, ht12, p535_1, u1ehi2]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          rcases p535_3 (m.d 0 2) (by simp) with h560 | h560
                                          · linarith only [h439, h560, hlam]
                                          · linarith only [h4, h560, hlam]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [h533, hlam, p535_1]
                                        · have p535_0 := h535c.1
                                          have p535_1 := h535c.2.1
                                          have p535_2 := h535c.2.2.1
                                          have p535_3 := h535c.2.2.2
                                          linarith only [hlam, p535_0]
                                      · linarith only [h2, h528, h529, h534, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                    · linarith only [h1, h4, h5, h533, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                              · linarith only [h5, h518, h528, hc24, hlam, hphi, ht12, u1ehi3]
                    · linarith only [h4, h5, h519, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h569 | h569
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h570 | h570
                      · linarith only [h0, h5, h518, h570, hc45, hlam, hphi, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h572 | h572
                        · linarith only [h0, h439, h572, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h574 | h574
                          · linarith only [h1, h4, h5, h518, h574, hc45, hlam, hphi, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h576 | h576
                            · linarith only [h1, h516, h576, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h578 | h578
                              · linarith only [h0, h5, h518, h578, hc14, hlam, hphi, u1ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h580 | h580
                                · linarith only [h1, h514, h569, h580, hc12, hlam, hphi, u1ehi2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h582 | h582
                                  · linarith only [h0, h1, h5, h516, h518, h569, h582, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h584 | h584
                                    · linarith only [h0, h5, h518, h569, h580, h584, hc23, hc34, hlam, hphi]
                                    · linarith only [h1, h4, h5, h584, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · linarith only [h4, h5, h569, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h588 | h588
          · rcases m.htr 0 2 5 (by decide) (by decide) with h589 | h589
            · rcases m.htr 0 3 4 (by decide) (by decide) with h590 | h590
              · rcases m.htr 0 3 5 (by decide) (by decide) with h591 | h591
                · rcases m.htr 0 4 5 (by decide) (by decide) with h592 | h592
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h593 | h593
                    · linarith only [h4, h588, h592, h593, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h595 | h595
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h596 | h596
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h597 | h597
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h598 | h598
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h599 | h599
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h600 | h600
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h601 | h601
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h602 | h602
                                    · linarith only [h0, h4, h595, h602, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                                    · linarith only [h2, h599, h600, h602, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                  · linarith only [h0, h4, h596, h601, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                                · linarith only [h0, h4, h596, h600, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                              · linarith only [h4, h588, h592, h599, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                            · linarith only [h591, h597, h598, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h4, h590, h593, h595, h597, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                        · linarith only [h4, h589, h595, h596, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · linarith only [h4, h588, h595, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h612 | h612
                    · linarith only [h4, h588, h612, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h614 | h614
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h615 | h615
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h616 | h616
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h617 | h617
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h618 | h618
                              · linarith only [h2, h592, h618, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h620 | h620
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h621 | h621
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h622 | h622
                                    · linarith only [h0, h4, h592, h614, h622, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h624 | h624
                                      · linarith only [h0, h2, h4, h592, h615, h620, h622, h624, hc23, hlam, hphi, ht12, u1ehi3]
                                      · rcases h2bigk with h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [hlam, p626_0]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [h4, hc12, hc23, hlam, hphi, p626_1]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [h4, hlam, p626_0]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [h4, h620, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p626_1, u4ehi3]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [h4, h620, h622, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p626_1, u4ehi3]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [h0, hlam, p626_1]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [hlam, p626_0]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [h612, hlam, p626_0]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [h0, h620, hc01, hlam, hphi, ht0b, ht45, ht5b, p626_1, u4ehi3]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [h0, h4, h620, h622, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p626_1, u4ehi3]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [h0, hc23, hlam, hphi, ht12, p626_1, u1ehi1]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [hc23, hlam, hphi, ht12, p626_1, u1ehi1]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [hlam, p626_0]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          rcases p626_3 (m.d 0 2) (by simp) with h640 | h640
                                          · linarith only [h4, h640, hlam]
                                          · linarith only [h588, h640, hlam]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          rcases p626_3 (m.d 0 2) (by simp) with h643 | h643
                                          · linarith only [h4, h643, hlam]
                                          · linarith only [h589, h643, hlam]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [h588, hlam, p626_0]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [h614, hlam, p626_0]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [h620, hlam, p626_0]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [hlam, p626_0]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [h622, hlam, p626_0]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [h589, hlam, p626_0]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [h615, hlam, p626_0]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [h621, hlam, p626_0]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [h0, h615, h620, hc02, hlam, hphi, ht0b, ht45, ht5b, p626_1, u4ehi3]
                                        · have p626_0 := h626c.1
                                          have p626_1 := h626c.2.1
                                          have p626_2 := h626c.2.2.1
                                          have p626_3 := h626c.2.2.2
                                          linarith only [hlam, p626_0]
                                  · linarith only [h1, h4, h617, h621, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · linarith only [h0, h4, h614, h620, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                            · linarith only [h4, h591, h617, hc23, hlam, hphi, ht12, u1ehi2]
                          · linarith only [h4, h590, h612, h614, h616, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                        · linarith only [h589, h614, h615, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h4, h588, h614, hc23, hlam, hphi, ht12, u1ehi1]
                · linarith only [h4, h589, h591, hlam]
              · linarith only [h4, h588, h590, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h664 | h664
              · rcases m.htr 0 3 5 (by decide) (by decide) with h665 | h665
                · rcases m.htr 0 4 5 (by decide) (by decide) with h666 | h666
                  · linarith only [h588, h589, h666, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h668 | h668
                    · linarith only [h0, h4, h668, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h670 | h670
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h671 | h671
                        · linarith only [h0, h589, h671, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h673 | h673
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h674 | h674
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h675 | h675
                              · linarith only [h2, h666, h675, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h677 | h677
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h678 | h678
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h679 | h679
                                    · linarith only [h0, h2, h589, h666, h670, h678, h679, hc23, hlam, hphi, ht12, u1ehi3]
                                    · linarith only [h0, h589, h670, h677, h679, hc45, hlam, hphi, u4ehi3]
                                  · linarith only [h0, h1, h4, h670, h674, h677, h678, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · linarith only [h0, h4, h670, h677, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                            · linarith only [h1, h665, h673, h674, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h4, h664, h668, h670, h673, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · linarith only [h588, h589, h670, hc25, hlam, hphi, ht12, u1ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h687 | h687
                  · linarith only [h4, h588, h665, h687, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h689 | h689
                    · linarith only [h4, h588, h689, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h691 | h691
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h692 | h692
                        · linarith only [h0, h589, h692, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h694 | h694
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h695 | h695
                            · linarith only [h0, h4, h665, h691, h695, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h697 | h697
                              · linarith only [h2, h687, h697, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h699 | h699
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h700 | h700
                                  · linarith only [h0, h4, h665, h691, h699, h700, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                  · linarith only [h0, h4, h691, h699, h700, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                                · linarith only [h0, h4, h691, h699, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                          · linarith only [h664, h665, h694, hc13, hc35, hlam, hphi]
                      · linarith only [h4, h588, h665, h691, hc35, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h4, h588, h664, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h707 | h707
            · rcases m.htr 0 3 4 (by decide) (by decide) with h708 | h708
              · rcases m.htr 0 3 5 (by decide) (by decide) with h709 | h709
                · rcases m.htr 0 4 5 (by decide) (by decide) with h710 | h710
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h711 | h711
                    · linarith only [h4, h707, h711, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h713 | h713
                      · linarith only [h588, h707, h713, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h715 | h715
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h716 | h716
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h717 | h717
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h718 | h718
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h719 | h719
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h720 | h720
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h721 | h721
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h722 | h722
                                      · linarith only [h1, h716, h722, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                      · linarith only [h0, h588, h715, h719, h721, h722, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                    · linarith only [h0, h588, h715, h721, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                                  · linarith only [h0, h588, h715, h719, h720, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                                · linarith only [h0, h4, h715, h719, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                              · linarith only [h588, h710, h718, hc24, hlam, hphi, ht12, u1ehi3]
                            · linarith only [h4, h709, h716, h717, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · linarith only [h4, h708, h711, h715, h716, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h4, h707, h715, hc12, hc23, hlam, hphi]
                  · linarith only [h588, h707, h710, hlam]
                · linarith only [h4, h707, h709, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h734 | h734
                · rcases m.htr 0 4 5 (by decide) (by decide) with h735 | h735
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h736 | h736
                    · linarith only [h4, h707, h736, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h738 | h738
                      · linarith only [h0, h588, h738, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h740 | h740
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h741 | h741
                          · linarith only [h0, h4, h708, h740, h741, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h743 | h743
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h744 | h744
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h745 | h745
                                · linarith only [h0, h4, h708, h740, h745, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                                · linarith only [h0, h4, h740, h745, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                              · linarith only [h588, h735, h744, hc24, hlam, hphi, ht12, u1ehi3]
                            · linarith only [h734, h736, h740, h743, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                        · linarith only [h4, h707, h708, h740, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h4, h707, h708, h735, hlam]
                · linarith only [h4, h707, h734, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h753 | h753
              · rcases m.htr 0 3 5 (by decide) (by decide) with h754 | h754
                · rcases m.htr 0 4 5 (by decide) (by decide) with h755 | h755
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h756 | h756
                    · linarith only [h0, h4, h756, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h758 | h758
                      · linarith only [h0, h588, h758, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h760 | h760
                        · linarith only [h0, h707, h760, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h762 | h762
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h763 | h763
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h764 | h764
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h765 | h765
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h766 | h766
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h767 | h767
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h768 | h768
                                      · linarith only [h1, h762, h768, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                      · linarith only [h2, h764, h768, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                    · linarith only [h1, h762, h764, h767, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                  · linarith only [h1, h588, h763, h765, h766, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · linarith only [h0, h4, h765, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h4, h753, h755, h764, hc23, hlam, hphi, ht12, u1ehi3]
                            · linarith only [h4, h754, h762, h763, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · linarith only [h4, h753, h756, h762, hc23, hlam, hphi, ht12, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h777 | h777
                    · linarith only [h0, h1, h4, h588, h755, h777, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h779 | h779
                      · linarith only [h0, h588, h779, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h781 | h781
                        · linarith only [h0, h707, h781, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h783 | h783
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h784 | h784
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h785 | h785
                              · linarith only [h0, h588, h755, h785, hc14, hlam, hphi, u1ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h787 | h787
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h788 | h788
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h789 | h789
                                    · linarith only [h0, h588, h755, h787, h789, hc23, hlam, hphi, ht12, u1ehi1]
                                    · linarith only [h0, h588, h789, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                  · linarith only [h0, h4, h788, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                                · linarith only [h0, h1, h4, h783, h787, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                            · linarith only [h4, h754, h784, hc23, hlam, hphi, ht12, u1ehi2]
                          · linarith only [h4, h753, h777, h783, hc23, hlam, hphi, ht12, u1ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h796 | h796
                  · linarith only [h753, h754, h796, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h798 | h798
                    · linarith only [h0, h4, h798, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h800 | h800
                      · linarith only [h0, h588, h800, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h802 | h802
                        · linarith only [h0, h707, h802, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h804 | h804
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h805 | h805
                            · linarith only [h1, h754, h805, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h807 | h807
                              · linarith only [h2, h796, h807, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h809 | h809
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h810 | h810
                                  · linarith only [h1, h754, h804, h810, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                  · linarith only [h0, h4, h810, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                                · linarith only [h0, h1, h4, h804, h809, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                          · linarith only [h753, h754, h804, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h815 | h815
                · rcases m.htr 0 4 5 (by decide) (by decide) with h816 | h816
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h817 | h817
                    · linarith only [h0, h4, h817, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h819 | h819
                      · linarith only [h0, h588, h819, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h821 | h821
                        · linarith only [h0, h707, h821, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h823 | h823
                          · linarith only [h1, h753, h815, h823, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h825 | h825
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h826 | h826
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h827 | h827
                                · linarith only [h3, h753, h815, h821, h827, hc23, hlam, hphi, ht12, u1ehi1]
                                · linarith only [h0, h4, h827, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h816, h823, h825, h826, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h4, h815, h825, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h753, h815, h816, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h833 | h833
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h834 | h834
                    · linarith only [h0, h4, h834, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h836 | h836
                      · linarith only [h0, h588, h836, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h838 | h838
                        · linarith only [h0, h707, h838, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h840 | h840
                          · linarith only [h1, h753, h840, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h842 | h842
                            · linarith only [h1, h815, h842, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h844 | h844
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h845 | h845
                                · linarith only [h1, h753, h834, h845, hc23, hlam, hphi, ht12, u1ehi1]
                                · linarith only [h0, h4, h845, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h588, h833, h844, hc24, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h849 | h849
                    · linarith only [h0, h4, h849, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h851 | h851
                      · linarith only [h0, h588, h851, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h853 | h853
                        · linarith only [h0, h707, h853, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h855 | h855
                          · linarith only [h1, h753, h833, h855, hc45, hlam, hphi, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h857 | h857
                            · linarith only [h1, h815, h857, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h859 | h859
                              · linarith only [h0, h4, h753, h833, h859, hc14, hlam, hphi, u1ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h861 | h861
                                · linarith only [h0, h4, h753, h861, hc23, hlam, hphi, ht12, u1ehi1]
                                · linarith only [h0, h4, h861, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
  · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]

end R2N4
